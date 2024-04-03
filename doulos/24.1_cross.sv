// Section 24.1: Cross

bit [3:0] A, B;
covergroup CG1 @(posedge clk);
  AxB : cross A, B; // Coverpoints are implicitly created for a and b
                    // Each coverpoint has 16 bins, auto[0] to auto[15]
     // AxB has 16*16 cross products, and each cross product is a bin of AxB
  BC  : coverpoint B + C; // Expression defined as coverpoint
  AxBC: cross A, BC;// Cross of an implicit coverpoint and an expression
endgroup


