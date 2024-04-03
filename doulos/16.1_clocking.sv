// Section 16.1: Clocking

clocking CB1 @(negedge Clk);
  default input #1ns output #2ns;
  input Q;
  output Enable, Data;
  output #1step UpDn = top.Counter.UpDn;
  output posedge Load	;
endclocking


