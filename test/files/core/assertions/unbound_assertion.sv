//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module unbound_assertion();
logic clk = 0;
logic req,reset, gnt;

always #1 clk ++;

//=================================================
// Sequence Layer
//=================================================
sequence req_gnt_seq;
  req ##[1:$] gnt;
endsequence
//=================================================
// Property Specification Layer
//=================================================
property req_gnt_prop;
  @ (posedge clk) 
    disable iff (reset)
      req |-> req_gnt_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
req_gnt_assert : assert property (req_gnt_prop);

initial begin
  $display("@%0dns Asserting reset",$time);
  reset <= 1;
  req <= 0;
  gnt <= 0;
  $display("@%0dns Deasserting reset",$time);
  #20 reset <= 0;
  // Make the assertion pass
  #100 @ (posedge clk) req  <= 1;
  $display("@%0dns Asserting req",$time);
  repeat (100) @(posedge clk);
  @ (posedge clk) req <= 0;
  $display("@%0dns Deasserting req",$time);
  repeat (2) @ (posedge clk);
  $display("@%0dns Asserting gnt",$time);
  gnt <= 1;
  @ (posedge clk) gnt <= 0;
  $display("@%0dns Deasserting gnt",$time);
  #100 @ (posedge clk) req  <= 1;
  $display("@%0dns Asserting req",$time);
  repeat (5) @ (posedge clk);
  req <= 0;
  $display("@%0dns Deasserting req",$time);
  #100 $finish;
end

endmodule
