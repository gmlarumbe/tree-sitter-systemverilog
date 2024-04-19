//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module binary_assertion();

logic clk = 0;
always #1 clk ++;

logic req,gnt,busy;
//=================================================
// Sequence Specification Layer
//=================================================
sequence s1;
 $past(!req,1) ##1 ($rose(gnt) and $past(!gnt,1));
endsequence

sequence s2;
 $past(!req,1) ##1 $rose(gnt) ##1 $fell(gnt);
endsequence 

sequence s3;
  req ##1 gnt ##1 busy ##1 (!req and !gnt and !busy);
endsequence

sequence s4;
  req ##[1:3] gnt;
endsequence
//=================================================
// Property Specification Layer
//=================================================
property and_prop;
  @ (posedge clk) 
    req |-> s1 and s2;
endproperty

property intersect_prop;
  @ (posedge clk) 
    req |-> s1 intersect s3;
endproperty

property or_prop;
  @ (posedge clk) 
    req |-> s1 or s4;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
and_assert       : assert property (and_prop);
intersect_assert : assert property (intersect_prop);
or_assert        : assert property (or_prop);
//=================================================
// Generate input vectors
//=================================================
initial begin
  req <= 0;gnt <= 0;busy<=0;
  repeat(10) @ (posedge clk);
  req <= 1;
  @( posedge clk);
  gnt <= 1;
  req <= 0;
  @( posedge clk);
  busy <= 1;
  // Make the assertion fail now
  // OR will not fail
  req <= 0;gnt <= 0; busy <= 0;
  repeat(10) @ (posedge clk);
  req <= 1;
  repeat (2) @( posedge clk);
  req <= 0;
  gnt <= 1;
  @( posedge clk);
  @( posedge clk);
  req <= 0;gnt <= 0; busy <= 0;
  // Terminate the sim
  #30 $finish;
end

endmodule
