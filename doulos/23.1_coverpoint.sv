// Section 23.1: Coverpoint

//Simple example
bit [3:0] X, Y;
covergroup CG @(posedge clk);
  P1: coverpoint X;
  P2: coverpoint Y;
endgroup


