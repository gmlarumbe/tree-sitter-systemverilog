module foo;

    // To bind with all instances of DUT
    bind D_flipflop assertion_dff all_inst(clk, rst_n, d, q);

    // To bind with single instance of DUT
    bind tb.dff2 assertion_dff single_inst(clk, rst_n, d, q);

    // To bind with single instance of DUT (with constant_bit_select)
    bind top.u_dut.u_blk_gen[asrt_inst].instname[0] my_assert u_my_assert (clk, rst_n, d, q);

    // To bind with single instance of DUT (with constant_bit_select)
    bind top[0][1].u_dut[1][2].u_blk_gen[2].instname[0] my_assert u_my_assert (clk, rst_n, d, q);

endmodule;
