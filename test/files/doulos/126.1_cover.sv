// Section 126.1: Cover

module Top(input bit clk);
  logic a, b;
  sequence s1;
    @(posedge clk) a ##1 b;
  endsequence
  Label1: cover property (s1);
  Label2: cover sequence (s1);  // Alternatively
  /*...*/
endmodule


