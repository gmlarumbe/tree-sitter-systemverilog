// Section 24.2: Cross

covergroup CG2 @(posedge clk);
  CP_A: coverpoint A
  {
    bins CP_A1 = {[0:4]};
    bins CP_A2 = {[5:8]};
  }
  CP_B: coverpoint B
  {
    bins CP_B1 = {[1:5]};
    bins CP_B2 = {[7:12]};
  }
  Cr  : cross CP_A, CP_B
  {
    ignore_bins  EB = binsof(CP_A) intersect {5, [1:3]};
    illegal_bins IB = binsof(CP_A) intersect {12};
  bins Cr1 = ! binsof(CP_A) intersect {[6:9]}; 
             // 2 cross products: <CP_A1, CP_B1>, <CP_A1,CP_B2>
  bins Cr2 = binsof(CP_A.CP_A2) && binsof(CP_B.CP_B1);
             // 1 cross product: <CP_A2, CP_B1>
  }
endgroup


