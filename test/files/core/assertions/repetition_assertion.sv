//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module repetition_assertion();

logic clk = 0;
always #1 clk ++;

logic req,busy,gnt;
//=================================================
// Sequence Layer
//=================================================
sequence boring_way_seq;
  req ##1 busy ##1 busy ##1 gnt;
endsequence

sequence cool_way_seq;
  req ##1 busy [*2] ##1 gnt;
endsequence

sequence range_seq;
  req ##1 busy [*1:5] ##1 gnt;
endsequence

//=================================================
// Property Specification Layer
//=================================================
property boring_way_prop;
  @ (posedge clk) 
      req |-> boring_way_seq;
endproperty

property cool_way_prop;
  @ (posedge clk) 
      req |-> cool_way_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
boring_way_assert : assert property (boring_way_prop);
cool_way_assert   : assert property (cool_way_prop);

//=================================================
// Generate input vectors
//=================================================
initial begin
  req <= 0; busy <= 0;gnt <= 0;
  @ (posedge clk);
  req <= 1;
  @ (posedge clk);
  busy <= 1;
  req  <= 0;
  repeat(2) @ (posedge clk);
  busy <= 0;
  gnt <= 1;
  @ (posedge clk);
  gnt <= 0;
  // Now make the assertion fail
  req <= 0; busy <= 0;gnt <= 0;
  @ (posedge clk);
  req <= 1;
  @ (posedge clk);
  busy <= 1;
  req  <= 0;
  repeat(3) @ (posedge clk);
  busy <= 0;
  gnt <= 1;
  @ (posedge clk);
  gnt <= 0;
  #30 $finish;
end

endmodule
