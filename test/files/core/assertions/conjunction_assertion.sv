//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module conjunction_assertion();

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
logic gnt2;
initial begin
  gnt2 <= 0; gnt <= 0;
end
always @ (posedge clk)
begin
  gnt2 <= req;
  gnt  <= gnt2;
end
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
// A conjunction property
//=================================================
property delay1;
    req ##1 gnt;
endproperty
property delay2;
    req ##2 gnt;
endproperty
// See the AND operator
property conjunction_prop;
  @ (posedge clk)
    delay1 and delay2;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
conjunction_assert : assert property (conjunction_prop);

endmodule
