//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module clock_resolve_assertion();
logic clk = 0;
logic req,gnt;
//=================================================
// Clock inside a sequence 
//=================================================
sequence req_gnt_seq;
  @ (posedge clk)
      req ##1 gnt;
endsequence
//=================================================
// Clock inside a property
//=================================================
property req_gnt_prop;
  @ (posedge clk)
      req |=> gnt;
endproperty
//=================================================
// Clock infered from a always block
//=================================================
always @ (posedge clk)
begin
   gnt <= req;
   //==============================================
   // Here clock is infered to be posedge clk
   //==============================================
   req_gnt_assert : assert property (req  |=> gnt);
end
//=================================================
// Default clocking
//=================================================
default clocking aclk @ (posedge clk);
  input req;
  input gnt;
endclocking

property req_gnt_default_prop;
   req |-> ##1 gnt;
endproperty
//=================================================
// clocking clocking
//=================================================
clocking reqclk @ (posedge clk);
  input req;
  input gnt;
endclocking

property req_gnt_clocking_prop;
   reqclk.req |-> ##1 reqclk.gnt;
endproperty
//+++++++++++++++++++++++++++++++++++++++++++++++++
// Now call all the assertion in one go
//+++++++++++++++++++++++++++++++++++++++++++++++++
a1  : assert property (req_gnt_prop);
a2  : assert property (req_gnt_default_prop);
a3  : assert property (req_gnt_clocking_prop);
//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Assertion testing code
//+++++++++++++++++++++++++++++++++++++++++++++++++
always #1 clk ++;

initial begin
  $monitor("Req %b Gnt %b",req,gnt);
  req <= 0; gnt <= 0;
  // Make the assertion pass
  ##1 req  <= 1;
  ##20;
  req <= 0;
  #10 $finish;
end

endmodule
