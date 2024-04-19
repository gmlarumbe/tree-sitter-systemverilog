//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module clock_assertion(
  input wire clk,req,reset, 
  output reg gnt);
//=================================================
// Sequence Layer
// Here clock is specified inside the sequence
//=================================================
sequence req_gnt_seq;
  @ (posedge clk) 
  (~req & gnt) ##1 (~req & ~gnt);
endsequence
//=================================================
// Property Specification Layer
// Still requires clock for the property
//=================================================
property req_gnt_prop;
  @ (posedge clk) 
    disable iff (reset)
      req |=> req_gnt_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
req_gnt_assert : assert property (req_gnt_prop)
                 else
                 $display("@%0dns Assertion Failed", $time);
//=================================================
// Actual DUT RTL
//=================================================
always @ (posedge clk)
  gnt <= req;

endmodule

//+++++++++++++++++++++++++++++++++++++++++++++++
//   Testbench Code
//+++++++++++++++++++++++++++++++++++++++++++++++
module concurrent_assertion_tb();

reg clk = 0;
reg reset, req = 0;
wire gnt;

always #3 clk ++;

initial begin
  reset <= 1;
  #20 reset <= 0;
  // Make the assertion pass
  #100 @ (posedge clk) req  <= 1;
  @ (posedge clk) req <= 0;
  // Make the assertion fail
  #100 @ (posedge clk) req  <= 1;
  repeat (2) @ (posedge clk);
  req <= 0;
  #10 $finish;
end

clock_assertion dut (clk,req,reset,gnt);

endmodule
