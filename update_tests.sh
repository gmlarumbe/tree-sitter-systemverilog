#!/bin/bash

RC=

while getopts :p:t opts; do
    case ${opts} in
        p) PATTERN=${OPTARG} ;;
        t) TREE_SITTER_TEST=true ;;
    esac
done

# First create the directory structure to prevent copy errors
TEST_DIR=test/files
TEST_SUBDIRS=( $(find $TEST_DIR -type d -exec realpath --relative-to $TEST_DIR {} \;) )

for dir in ${TEST_SUBDIRS[@]}; do
    mkdir -p test/corpus/$dir &
done
wait

# Find all SystemVerilog test files in test directory
FILES_SV=( $( cd $TEST_DIR && find * -type f -name "*.sv" -o -name "*.svh" -o -name "*.v" -o -name "*.vh") )


# Expected failure tests
EXPECTED_FAIL_FILELIST=(core/subroutines/call_method_cond_expr_rhs_assignment_ERROR.sv
                        core/subroutines/randomize_cond_expr_rhs_assignment_ERROR.sv
                        sv-tests/chapter-5/5.6--wrong-identifiers.sv
                        sv-tests/chapter-5/5.6.4--compiler-directives-begin-keywords.sv
                        sv-tests/chapter-5/5.7.1--integers-signed-illegal.sv
                        sv-tests/chapter-5/5.7.1--integers-unsized-illegal.sv
                        sv-tests/chapter-5/5.7.2-real-constants-illegal.sv
                        sv-tests/chapter-5/5.10-structure-arrays-illegal.sv
                        sv-tests/chapter-6/6.9.2--vector_vectored_inv.sv
                        sv-tests/chapter-11/11.3.6--assign_in_expr_inv.sv
                        sv-tests/chapter-22/22.5.1--define-expansion_21.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-1.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-2.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-3.sv
                        sv-tests/chapter-22/22.11--pragma-invalid.sv
                        sv-tests/chapter-22/22.12--line-illegal-1.sv
                        sv-tests/chapter-22/22.12--line-illegal-2.sv
                        sv-tests/chapter-22/22.12--line-illegal-3.sv
                        sv-tests/chapter-22/22.12--line-illegal-4.sv
                        sv-tests/chapter-22/22.12--line-illegal-5.sv
                        sv-tests/sanity.sv
                        doulos/69.2_name.sv
                        doulos/73.3_number.sv
                        doulos/116.1_begin_keywords.sv
                        # TODO:
                        # sv-tests/chapter-22/22.3--resetall_illegal.sv
                       )

# Excluded tests
EXCLUDED_FILELIST=(sv-tests/chapter-5/5.6.4--compiler-directives-preprocessor-macro_0.sv # No intention of supporting preprocessing
                   sv-tests/chapter-5/5.10-structure-arrays-illegal.sv                   # No intention of detecting the /* C-like assignment is illegal */ for struct initialization
                   sv-tests/chapter-11/11.4.14.3--unpack_stream_inv.sv                   # No intention of parse the width of the streaming assignment target
                   sv-tests/chapter-22/22.4--check_included_definitions.sv               # TODO: Detects `define_var as macro definition instead of macro usage after adding directives as reserved keywords
                   sv-tests/chapter-22/22.5.1--define-expansion_25.sv                    # No intention of supporting parsing of macro expansion of string values
                   sv-tests/generic/preproc/preproc_test_2.sv                            # No intention of supporting expansion with ifdef/ifndef
                   # UVM
                   uvm/1800.2-2020-2.0/src/base/uvm_traversal.svh # ifdef conditional compilation breaks seq_block declaration -> statements order
                   uvm/1800.2-2020-2.0/src/tlm1/uvm_tlm_fifos.svh # ifdef conditional compilation breaks seq_block declaration -> statements order
                   uvm/1800.2-2020-2.0/src/reg/uvm_reg_field.svh  # reg_field has an embedded text_macro_usage inside a $.hex_number
                   # Doulos reference examples
                   doulos/8.3_attribute.sv                   # This one should actually work but it doesn't for some reason (doesn't detect it as a tf_call)
                   doulos/11.1_bind_\(operator_overload\).sv # Deprecated in 1800-2017
                   doulos/52.2_import_dpi-c.sv               # Don't parse C code
                   doulos/35.2_export_dpi-c.sv               # Don't parse C code
                   doulos/61.2_let.sv                        # Complex let construct, macro-like (come back if integrating $.let_expression with dynamic precedence)
                   doulos/117.1_define.sv
                   doulos/117.2_define.sv
                   doulos/135.5_sequence.sv                  # Multiclock assertion with syntax errors
                   # Pulp AXI
                   pulp_axi/src/axi_demux_simple.sv     # Not supporting |-> on macro usage (line 505)
                   pulp_axi/src/axi_interleaved_xbar.sv # Preprocessing on the last parameter/port, too much effort on handling the comma
                   pulp_axi/src/axi_xbar.sv             # Preprocessing on the last parameter/port, too much effort on handling the comma
                   # CVA6
                   cva6/SyncDpRam.sv                  # Conditional directives
                   cva6/SyncSpRam.sv                  # Conditional directives
                   cva6/SyncSpRamBeNx32.sv            # Conditional directives
                   cva6/SyncSpRamBeNx64.sv            # Conditional directives
                   cva6/SyncTpRam.sv                  # Conditional directives
                   cva6/ariane_xilinx.sv              # Conditional directives
                   cva6/riscv_core_setting.sv         # Conditional directives
                   cva6/riscv_custom_instr_enum.sv    # Include file for enum elements
                   cva6/cva6_tb_wrapper.sv            # Usage of keyword as function arg
                   cva6/tb_dcache_pkg.sv              # Usage of keyword as function arg
                   cva6/cva6_rvfi.sv                  # Complex macros (WITH, COMMA)
                   cva6/uvme_cvxif_covg.sv            # Complex macros (WITH, COMMA)
                   cva6/uvme_isa_covg.sv              # Complex macros (WITH, COMMA)
                   cva6/issue_read_operands.sv        # Not sure, a bit complex
                   cva6/tb_div.sv                     # for snippet detected as for generate
                   cva6/tb_rem.sv                     # for snippet detected as for generate
                   cva6/tb_udiv.sv                    # for snippet detected as for generate
                   cva6/tb_urem.sv                    # for snippet detected as for generate
                   cva6/uvma_interrupt_seq.sv         # Various, use of automatic in external task, dot element for time delay
                   cva6/sram.sv                       # MISSING "always", but it's a generate!
                   cva6/uvma_cva6_core_cntrl_cntxt.sv # MISSING "end" due to pragma protects wrong detection
                   # basejump_stl/
                   basejump_stl/bsg_async/bsg_launch_sync_sync.sv                                   # Keyword in macro, else in macro
                   basejump_stl/bsg_async/bsg_sync_sync.sv                                          # else in macro
                   basejump_stl/bsg_comm_link/test_bsg_comm_link_checker.sv                         # Macro with complex prefix with space
                   basejump_stl/bsg_comm_link/tests/test_bsg_assembler/test_bsg_assembler.sv        # Static cast with system_tf $clog2(num_channels_lp)'
                   basejump_stl/bsg_comm_link/tests/test_bsg_comm_link/test_bsg_comm_link.sv        # Use of checker keyword as instance name
                   basejump_stl/bsg_dmc/bsg_dmc_phy.sv                                              # Macro usage with arg with spaces
                   basejump_stl/bsg_dmc/bsg_dmc_xilinx_ui_trace_replay.sv                           # Macro usage for static cast
                   basejump_stl/bsg_legacy/bsg_chip/bsg_nonsynth_mixin_motherboard.v                # Macro usage for module names
                   basejump_stl/bsg_legacy/bsg_chip/bsg_rocket/bsg_chip_rocket.v                    # Syntax errors in code
                   basejump_stl/bsg_legacy/bsg_chip/bsg_rocket/bsg_nonsynth_chipset_rocket_fsb.v    # Syntax errors in code
                   basejump_stl/bsg_legacy/bsg_chip/bsg_rocket/bsg_rocket_core_fsb.v                # Missing name of instance for bsg_fsb_to_htif_connector
                   basejump_stl/bsg_legacy/bsg_tag/config_net/sim/send_config_tag.v                 # Include missing ""
                   basejump_stl/bsg_mem/bsg_mem_multiport_latch_write_banked_bypassing.sv           # Extra end
                   basejump_stl/bsg_misc/bsg_encode_one_hot.sv                                      # Time as macro arg
                   basejump_stl/bsg_misc/bsg_round_robin_arb.sv                                     # Macro with ~ before usage
                   basejump_stl/bsg_misc/bsg_scan.sv                                                # Time as macro arg
                   basejump_stl/bsg_test/bsg_nonsynth_dpi_clock_gen.sv                              # Data type as macro arg
                   basejump_stl/bsg_test/bsg_nonsynth_dramsim3_map.sv                               # Macro usage as static cast type
                   basejump_stl/bsg_test/bsg_nonsynth_profiler.sv                                   # Parameter RHS is empty array '{}
                   basejump_stl/bsg_test/bsg_nonsynth_dramsim3.sv                                   # Macro with data type as arg
                   basejump_stl/experimental/bsg_dataflow/bsg_fifo_reorder_sync.sv                  # Macro usage with ! (!`BSG_IS_POW2(els_p))
                   basejump_stl/experimental/bsg_dataflow/bsg_fifo_reorder_sync_variable.sv         #  Macro usage with ! (!`BSG_IS_POW2(els_p))
                   basejump_stl/hard/gf_14/bsg_async/bsg_launch_sync_sync.sv                        # Keyword in macro, else in macro
                   basejump_stl/hard/gf_14/bsg_async/bsg_sync_sync.sv                               # else in macro
                   basejump_stl/hard/pickle_40/bsg_mem/bsg_mem_1rw_sync.sv                          # else in macro
                   basejump_stl/hard/pickle_40/bsg_mem/bsg_mem_1rw_sync_mask_write_bit.sv           # else in macro
                   basejump_stl/hard/pickle_40/bsg_mem/bsg_mem_1rw_sync_mask_write_byte.sv          # else in macro
                   basejump_stl/hard/pickle_40/bsg_mem/bsg_mem_2r1w_sync.sv                         # else in macro
                   basejump_stl/hard/saed_90/bsg_mem/bsg_mem_1r1w.sv                                # else in macro
                   basejump_stl/hard/saed_90/bsg_mem/bsg_mem_1r1w_sync.sv                           # else in macro
                   basejump_stl/hard/saed_90/bsg_mem/bsg_mem_1rw_sync.sv                            # else in macro
                   basejump_stl/hard/saed_90/bsg_mem/bsg_mem_1rw_sync_mask_write_bit.sv             # else in macro
                   basejump_stl/hard/saed_90/bsg_mem/bsg_mem_1rw_sync_mask_write_byte.sv            # else in macro
                   basejump_stl/hard/tsmc_16/bsg_async/bsg_launch_sync_sync.sv                      # Keyword in macro, else in macro
                   basejump_stl/hard/tsmc_16/bsg_async/bsg_sync_sync.sv                             # else in macro
                   basejump_stl/hard/tsmc_16/bsg_mem/bsg_mem_1r1w_sync_mask_write_bit.sv            # else in macro
                   basejump_stl/hard/tsmc_16/bsg_mem/bsg_mem_1rw_sync.sv                            # else in macro
                   basejump_stl/hard/tsmc_16/bsg_mem/bsg_mem_1rw_sync_mask_write_bit.sv             # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_dataflow/bsg_fifo_shift_datapath.sv           # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_mem/bsg_mem_1r1w.sv                           # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_mem/bsg_mem_1r1w_sync_mask_write_bit.sv       # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_mem/bsg_mem_1rw_sync.sv                       # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_mem/bsg_mem_1rw_sync_mask_write_bit.sv        # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_mem/bsg_mem_2r1w.sv                           # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_and.sv                               # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_buf.sv                               # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_clkbuf.sv                            # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_dff.sv                               # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_dff_en.sv                            # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_dff_reset.sv                         # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_dff_reset_en.sv                      # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_inv.sv                               # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_mul/bsg_mul_and_csa_block_hard.sv    # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_mul/bsg_mul_booth_4_block_rep.sv     # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_mul/bsg_mul_comp42_rep.sv            # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_mux.sv                               # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_mux_one_hot.sv                       # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_nand.sv                              # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_nor3.sv                              # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_reduce.sv                            # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_tiehi.sv                             # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_tielo.sv                             # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_xnor.sv                              # else in macro
                   basejump_stl/hard/tsmc_180_250/bsg_misc/bsg_xor.sv                               # else in macro
                   basejump_stl/hard/tsmc_28/bsg_async/bsg_launch_sync_sync.sv                      # Keyword in macro, else in macro
                   basejump_stl/hard/tsmc_28/bsg_async/bsg_sync_sync.sv                             # else in macro
                   basejump_stl/hard/tsmc_28/bsg_misc/bsg_buf.sv                                    # else in macro
                   basejump_stl/hard/tsmc_28/bsg_misc/bsg_dff.sv                                    # else in macro
                   basejump_stl/hard/tsmc_28/bsg_misc/bsg_nand.sv                                   # else in macro
                   basejump_stl/hard/tsmc_28/bsg_misc/bsg_nor3.sv                                   # else in macro
                   basejump_stl/hard/tsmc_28/bsg_misc/bsg_xnor.sv                                   # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_1r1w.sv                                # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_1r1w_sync.sv                           # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_1r1w_sync_mask_write_bit.sv            # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_1rw_sync.sv                            # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_1rw_sync_mask_write_bit.sv             # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_1rw_sync_mask_write_byte.sv            # else in macro
                   basejump_stl/hard/tsmc_40/bsg_mem/bsg_mem_2r1w.sv                                # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_and.sv                                    # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_buf.sv                                    # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_clkbuf.sv                                 # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_dff.sv                                    # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_dff_en.sv                                 # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_dff_reset.sv                              # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_dff_reset_en.sv                           # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_inv.sv                                    # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_mul/bsg_mul_and_csa_block_hard.sv         # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_mul/bsg_mul_booth_4_block_rep.sv          # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_mul/bsg_mul_comp42_rep.sv                 # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_mux.sv                                    # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_mux_one_hot.sv                            # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_nand.sv                                   # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_nor3.sv                                   # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_reduce.sv                                 # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_tiehi.sv                                  # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_tielo.sv                                  # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_xnor.sv                                   # else in macro
                   basejump_stl/hard/tsmc_40/bsg_misc/bsg_xor.sv                                    # else in macro
                   basejump_stl/hard/ultrascale_plus/bsg_async/bsg_launch_sync_sync.sv              # Keyword in macro, else in macro
                   basejump_stl/testing/bsg_cache/dmc/bsg_trace_rom.sv                              # else in macro
                   basejump_stl/testing/bsg_cache/lock_test/testbench.sv                            # Use of keyword 'checker' as an identifier
                   basejump_stl/testing/bsg_cache/regression_64/testbench.sv                        # Use of keyword 'checker' as an identifier
                   basejump_stl/testing/bsg_cache/regression_non_blocking/testbench.sv              # Use of keyword 'checker' as an identifier
                   basejump_stl/testing/bsg_cache/regression_v2/testbench.sv                        # Use of keyword 'checker' as an identifier
                   basejump_stl/testing/bsg_cache/wormhole_fanout/testbench.sv                      # Use of keyword 'checker' as an identifier
                   basejump_stl/testing/bsg_cache/wormhole_stream/testbench.sv                      # Use of keyword 'checker' as an identifier
                   basejump_stl/testing/bsg_dmc/lpddr_verilog_model/mobile_ddr.sv                   # Use of weird macro, and custom system tasks with args with spaces
                   basejump_stl/testing/bsg_dmc/lpddr_verilog_model/mobile_ddr_mcp.sv               # Use of weird macro
                   basejump_stl/testing/bsg_dmc/lpddr_verilog_model/tb.sv                           # Use of weird macro
                   basejump_stl/testing/bsg_dmc/traffic_generator.sv                                # Missing range for packed dimension
                   basejump_stl/testing/bsg_misc/bsg_counter_clock_downsample/test_bsg.sv           # Weird macro `WIDTH_P'd0;
                   basejump_stl/testing/bsg_misc/bsg_mux/test_bsg.sv                                # Macro usage for static cast
                   basejump_stl/testing/bsg_misc/bsg_rotate_left/main.sv                            # Macro usage for static cast
                   basejump_stl/testing/bsg_noc/bsg_mesh_to_ring_stitch/test_mesh_to_ring_stitch.sv # Static cast with system_tf
                   basejump_stl/testing/bsg_test/bsg_nonsynth_dramsim3/testbench.sv                 # Usage of macro for package import
                   basejump_stl/testing/bsg_test/bsg_nonsynth_dramsim3/testbench_multi.sv           # Usage of macro for package import
                   basejump_stl/testing/bsg_test/dramsim3_bandwidth/testbench.sv                    # Usage of macro for package import
                   basejump_stl/testing/bsg_test/dramsim3_bandwidth2/testbench.sv                   # Usage of macro for package import
                   # TODO:
                   sv-tests/chapter-22/22.3--resetall_illegal.sv
                   github/issue_34.sv
                   core/bit_select/complex_4.sv
                   core/directives/macro_2.sv         # Detects `define_var as macro definition instead of macro usage after adding directives as reserved keywords (same as sv-tests/chapter-22/22.4--check_included_definitions.sv)
                   core/directives/macro_keyword_1.sv # reserved('macros') still not working
                   core/directives/macro_keyword_2.sv # reserved('macros') still not working
                  )

# Filter tests, if there was an argument provided
if [[ -n "$PATTERN" ]]; then
    FILES_SV=( $( printf '%s\n' "${FILES_SV[@]}" | grep "$PATTERN" ) )
    echo "Filtering with regexp: $PATTERN"
fi


process_file(){
    local FILE=$1
    local INPUT_FILE=$TEST_DIR/$FILE

    local DIR_FILENAME=$(dirname $FILE)
    local BASE_FILENAME=$(basename $FILE)
    local FILENAME_NO_EXT="${BASE_FILENAME%.*}"
    local DEST_FILE=test/corpus/$DIR_FILENAME/${FILENAME_NO_EXT}.txt
    local LAST_FILE_LINE=

    if [[ "${EXCLUDED_FILELIST[@]}" =~ "$FILE" ]]; then
        echo "Excluding $FILE ..."
        cat $INPUT_FILE > $DEST_FILE
    else
        echo "============================================" > $DEST_FILE
        echo "$DIR_FILENAME/$FILENAME_NO_EXT" >> $DEST_FILE
        [[ "${EXPECTED_FAIL_FILELIST[@]}" =~ "$FILE" ]] && echo ":error" >> $DEST_FILE
        echo "============================================" >> $DEST_FILE
        echo "" >> $DEST_FILE

        cat $INPUT_FILE >> $DEST_FILE
        echo "" >> $DEST_FILE
        echo "----" >> $DEST_FILE
        echo "" >> $DEST_FILE

        tree-sitter parse $INPUT_FILE >> $DEST_FILE
        sed -i -E 's/ \[[0-9]+, [0-9]+\] - \[[0-9]+, [0-9]+\]//g' $DEST_FILE # Remove brackets with node positions

        # Check if file has errors and reformat expected file in that case (remove last line)
        LAST_FILE_LINE=$(tail -1 $DEST_FILE | grep -E 'ERROR|MISSING')
        if [[ $LAST_FILE_LINE ]]; then
            # Remove last file line before formatting
            sed -i '$ d' $DEST_FILE
            # Set new last file line without statistics
            LAST_FILE_LINE=$(echo $LAST_FILE_LINE | cut -d " " -f 7-)
            echo "" >> $DEST_FILE
            echo "$LAST_FILE_LINE" >> $DEST_FILE
        fi

        echo "Updated $DEST_FILE"
    fi
}


# Create and process tests in parallel
for file in "${FILES_SV[@]}"; do
    process_file $file &
done

wait
echo "Finished!"
echo ""

if [[ -n "$TREE_SITTER_TEST" ]]; then
    echo "Running tree-sitter tests..."
    tree-sitter test -i "$PATTERN" > test.log
    RC=$?
    if [[ $RC != 0 ]]; then
        echo "Some tests failed!!"
        cat test.log
    fi
fi

echo ""
echo "List of changed files:"
git submodule foreach git status --porcelain -uno
echo ""

# Report if all tests have passed
if [[ $RC -eq 0 ]]; then
    echo "All tests passed!"
else
    echo "Some tests failed!!"
fi
