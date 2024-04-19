//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module disjunction_assertion();

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
// A disjunction property
//=================================================
property delay1;
    req ##1 gnt;
endproperty
property delay2;
    req ##2 gnt;
endproperty
// See the OR operator
property disjunction_prop;
  @ (posedge clk)
    delay1 or delay2;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
disjunction_assert : assert property (disjunction_prop);

endmodule
