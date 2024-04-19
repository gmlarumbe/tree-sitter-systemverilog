//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module negation_assertion();

logic req,gnt,clk;
//=================================================
//  Clock generator
//=================================================
initial begin
 clk = 0; 
 forever #1 clk ++;
end
//=================================================
// Simple DUT behaviour
//=================================================
always @ (posedge clk)
  gnt <= req;
//=================================================
// Test Vector generation
//=================================================
initial begin
  req <= 0;
  #3 req <= 1;
  #5 req <= 0;
  #1 $finish;
end
//=================================================
// A negation property
//=================================================
property negation_prop;
  @ (posedge clk)
    not (req ##1 gnt);
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
negation_assert : assert property (negation_prop);

endmodule
