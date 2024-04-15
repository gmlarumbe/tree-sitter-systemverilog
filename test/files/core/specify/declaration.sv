specify
    specparam tRise_clk_q = 150, tFall_clk_q = 200;
    specparam tSetup = 70;

    (clk => q) = (tRise_clk_q, tFall_clk_q);

    $setup(d, posedge clk, tSetup);
endspecify
