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
                        sv-tests/chapter-22/22.11--pragma-invalid.sv
                        sv-tests/chapter-22/22.12--line-illegal-1.sv
                        sv-tests/chapter-22/22.12--line-illegal-2.sv
                        sv-tests/chapter-22/22.12--line-illegal-3.sv
                        sv-tests/chapter-22/22.12--line-illegal-4.sv
                        sv-tests/chapter-22/22.12--line-illegal-5.sv
                        sv-tests/chapter-22/22.5.1--define-expansion_21.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-1.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-2.sv
                        sv-tests/chapter-22/22.9--unconnected_drive-invalid-3.sv
                        sv-tests/sanity.sv
                        doulos/69.2_name.sv
                        doulos/73.3_number.sv
                        doulos/116.1_begin_keywords.sv
                       )

# Excluded tests
EXCLUDED_FILELIST=(sv-tests/chapter-5/5.6.4--compiler-directives-preprocessor-macro_0.sv # No intention of supporting preprocessing
                   sv-tests/chapter-5/5.10-structure-arrays-illegal.sv                   # No intention of detecting the /* C-like assignment is illegal */ for struct initialization
                   sv-tests/chapter-11/11.4.14.3--unpack_stream_inv.sv                   # No intention of parse the width of the streaming assignment target
                   sv-tests/chapter-22/22.5.1--define-expansion_20.sv                    # No intention of supporting parsing of macro expansion
                   sv-tests/chapter-22/22.5.1--define-expansion_25.sv                    # No intention of supporting parsing of macro expansion of string values
                   # No intention of supporting expansion with ifdef/ifndef
                   sv-tests/generic/preproc/preproc_test_2.sv
                   sv-tests/generic/typedef/typedef_test_26.sv
                   sv-tests/generic/typedef/typedef_test_27.sv
                   # ifdef conditional compilation breaks seq_block declaration -> statements order
                   uvm/1800.2-2020-2.0/src/base/uvm_traversal.svh
                   uvm/1800.2-2020-2.0/src/tlm1/uvm_tlm_fifos.svh
                   # reg_field has an embedded text_macro_usage inside a $.hex_number
                   uvm/1800.2-2020-2.0/src/reg/uvm_reg_field.svh
                   # Doulos reference examples
                   doulos/117.1_define.sv
                   doulos/117.2_define.sv
                   doulos/11.1_bind_\(operator_overload\).sv # Deprecated in 1800-2017
                   doulos/135.5_sequence.sv                  # Multiclock assertion with syntax errors
                   doulos/135.5_sequence.sv                  # Multiclock assertion with syntax errors
                   doulos/35.2_export_dpi-c.sv               # Don't parse C code
                   doulos/52.2_import_dpi-c.sv               # Don't parse C code
                   # Pulp AXI
                   pulp_axi/src/axi_demux_simple.sv     # Not supporting |-> on macro usage (line 505)
                   pulp_axi/src/axi_interleaved_xbar.sv # Preprocessing on the last parameter/port, too much effort on handling the comma
                   pulp_axi/src/axi_xbar.sv             # Preprocessing on the last parameter/port, too much effort on handling the comma
                   #################################################################
                   # TODO: The ones below are to be added after grammar.js cleanup #
                   #################################################################
                   # Let
                   doulos/61.2_let.sv # Complex let construct, macro-like (come back if integrating $.let_expression with dynamic precedence)
                   # Attribute
                   doulos/8.3_attribute.sv # TODO: This one should actually work but it doesn't for some reason (doesn't detect it as a tf_call)
                   # Conditional directives
                   cva6/SyncDpRam.sv
                   cva6/SyncSpRam.sv
                   cva6/SyncSpRamBeNx32.sv
                   cva6/SyncSpRamBeNx64.sv
                   cva6/SyncTpRam.sv
                   cva6/ariane_xilinx.sv
                   cva6/riscv_core_setting.sv
                   # Include file for enum elements
                   cva6/riscv_custom_instr_enum.sv
                   # Usage of keyword as function arg
                   cva6/cva6_tb_wrapper.sv
                   cva6/tb_dcache_pkg.sv
                   # Complex macros (WITH, COMMA)
                   cva6/cva6_rvfi.sv
                   cva6/uvme_cvxif_covg.sv
                   cva6/uvme_isa_covg.sv
                   # Others
                   cva6/issue_read_operands.sv # Not sure, a bit complex
                   cva6/tb_div.sv  # for snippet detected as for generate
                   cva6/tb_rem.sv  # for snippet detected as for generate
                   cva6/tb_udiv.sv # for snippet detected as for generate
                   cva6/tb_urem.sv # for snippet detected as for generate
                   cva6/uvma_interrupt_seq.sv # Various, use of automatic in external task, dot element for time delay
                   # TODO: No errors but missing something with tree-sitter parse/test
                   cva6/sram.sv                       # MISSING "always", but it's a generate!
                   cva6/uvma_cva6_core_cntrl_cntxt.sv # MISSING "end" due to pragma protects wrong detection
                   # TODO:
                   core/bit_select/complex_4.sv
                   github/issue_32.sv
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
git status --porcelain -uno test/corpus
echo ""

# Report if all tests have passed
if [[ $RC -eq 0 ]]; then
    echo "All tests passed!"
else
    echo "Some tests failed!!"
fi
