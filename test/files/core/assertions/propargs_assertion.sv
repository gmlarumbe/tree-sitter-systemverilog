//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module propargs_assertion();
logic clk = 0;
logic req,gnt;
logic a,b;
//=================================================
// Sequence Layer with args (NO TYPE)
//=================================================
sequence notype_seq (X, Y);
  (~X & Y) ##1 (~X & ~Y);
endsequence
//=================================================
// Sequence Layer with args (NO TYPE)
//=================================================
sequence withtype_seq (X, Y);
  (~X & Y) ##1 (~X & ~Y);
endsequence
//=================================================
// Property Specification Layer
//=================================================
property req_gnt_notype_prop;
  @ (posedge clk) 
      req |=> notype_seq(req,gnt);
endproperty

property req_gnt_type_prop;
  @ (posedge clk) 
      req |=> withtype_seq(req,gnt);
endproperty

property a_b_notype_prop;
  @ (posedge clk) 
      a |=> notype_seq(a,b);
endproperty

property a_b_type_prop;
  @ (posedge clk) 
      a |=> withtype_seq(a,b);
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
req_gnt_notype_assert : assert property (req_gnt_notype_prop);
req_gnt_type_assert   : assert property (req_gnt_type_prop);
a_b_notype_assert     : assert property (a_b_notype_prop);
a_b_type_assert       : assert property (a_b_type_prop);
//=================================================
// Actual DUT RTL
//=================================================
always @ (posedge clk)
  gnt <= req;

always @ (posedge clk)
  b <= a;

//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Assertion testing code
//+++++++++++++++++++++++++++++++++++++++++++++++++
always #3 clk ++;

initial begin
  // Make the assertion pass
  #100 @ (posedge clk) req  <= 1;
  @ (posedge clk) req <= 0;
  // Make the assertion fail
  #100 @ (posedge clk) req  <= 1;
  repeat (2) @ (posedge clk);
  req <= 0;

  // Make the assertion pass
  #100 @ (posedge clk) a  <= 1;
  @ (posedge clk) a <= 0;
  // Make the assertion fail
  #100 @ (posedge clk) a  <= 1;
  repeat (2) @ (posedge clk);
  a <= 0;
  #10 $finish;
end

endmodule
