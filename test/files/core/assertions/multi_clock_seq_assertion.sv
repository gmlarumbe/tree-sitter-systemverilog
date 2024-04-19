//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module multi_clock_seq_assertion();
logic clk1 = 0;
logic clk2 = 0;
logic req;
logic gnt;
//=================================================
// Sequence Specification Layer
//=================================================
sequence multi_clock_seq;
   @(posedge clk1) req ##1 @(posedge clk2) gnt;
endsequence
//=================================================
// Property Specification Layer
//=================================================
property multi_clock_prop;
  @ (posedge clk1)
      req |-> multi_clock_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
multi_clock_assert : assert property (multi_clock_prop);
//=================================================
// Here gnt is driven with respect to CLK2
//=================================================
initial begin
  #20 gnt <= 1;
  #120 gnt <= 0;
end
//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Assertion testing code
//+++++++++++++++++++++++++++++++++++++++++++++++++
initial begin
  // Make the assertion pass
  req  <= 0; gnt <= 0;
  #100 @ (posedge clk1) req  <= 1;
  repeat (20) @ (posedge clk1);
  req <= 0;
  #10 $finish;
end

always #1   clk1 ++;
always #6.1 clk2 ++;

endmodule
