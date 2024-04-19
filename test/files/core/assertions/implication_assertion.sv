//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module implication_assertion();

logic clk = 0;
always #1 clk ++;

logic req,busy,gnt;
//=================================================
// Sequence Layer
//=================================================
sequence implication_seq;
  req ##1 (busy [->3]) ##1 gnt;
endsequence

//=================================================
// Property Specification Layer
//=================================================
property overlap_prop;
  @ (posedge clk) 
      req |-> implication_seq;
endproperty

property nonoverlap_prop;
  @ (posedge clk) 
      req |=> implication_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
overlap_assert    : assert property (overlap_prop);
nonoverlap_assert : assert property (nonoverlap_prop);

//=================================================
// Generate input vectors
//=================================================
initial begin
  // Pass sequence
  gen_seq(3,0); 
  repeat (20) @ (posedge clk);
  // Fail sequence (gnt is not asserted properly)
  gen_seq(3,1); 
  // Terminate the sim
  #30 $finish;
end
//=================================================
/// Task to generate input sequence
//=================================================
task  gen_seq (int busy_delay,int gnt_delay);
  req <= 0; busy <= 0;gnt <= 0;
  @ (posedge clk);
  req <= 1;
  @ (posedge clk);
  req  <= 0;
  repeat (busy_delay) begin
   @ (posedge clk);
    busy <= 1;
   @ (posedge clk);
    busy <= 0;
  end
  repeat (gnt_delay) @ (posedge clk);
  gnt <= 1;
  @ (posedge clk);
  gnt <= 0;
endtask

endmodule
