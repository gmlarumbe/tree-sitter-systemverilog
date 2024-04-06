// Section 135.5: Sequence

// Clock flow
property P;
  @(posedge clk) x ##1 y |=>
  if (z)
    j |=> @(posedge clk1) k; // k is clocked at posedge clk1
  else                       // x, y, z, j, m are clocked at posedge clk
    m |=> @(posedge clk2) n; // n is clocked at posedge clk2
endproperty

