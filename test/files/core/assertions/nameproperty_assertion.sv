//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module nameproperty_assertion();

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
// One property called inside another property
//=================================================
property vanila_prop;
   req ##1 gnt;
endproperty

property nameproperty_prop;
  @ (posedge clk)
    vanila_prop;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
nameproperty_assert : assert property (nameproperty_prop);

endmodule
