//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module hash_sequence();

logic clk = 0;
always #1 clk ++;

logic [2:0] req,gnt;
logic reset;
//=================================================
// Shows basic usage of ## delay operator
//=================================================
sequence req_gnt_1clock_seq;
  req[0] ##1 gnt[0];
endsequence
//=================================================
// Shows range usage of ## delay operator
//=================================================
sequence req_gnt_3to5clock_seq;
  req[1] ##[3:5] gnt[1];
endsequence
//=================================================
// Shows zero delay usage of ## delay operator
//=================================================
sequence req_gnt_0clock_seq;
  req[2] ##0 gnt[2];
endsequence
//=================================================
// Shows sequence called within sequence 
//=================================================
sequence master_seq;
  req_gnt_1clock_seq ##1 req_gnt_3to5clock_seq ##1 req_gnt_0clock_seq;
endsequence
//=================================================
//  Declare property for each of sequence
//  We may use more then one seuqnce in a property
//=================================================
property req_gnt_1clock_prop;
  @ (posedge clk)
  disable iff (reset)
     req[0] |-> req_gnt_1clock_seq;
endproperty

property req_gnt_3to5clock_prop;
  @ (posedge clk)
  disable iff (reset)
     req[1] |-> req_gnt_3to5clock_seq;
endproperty

property req_gnt_0clock_prop;
  @ (posedge clk)
  disable iff (reset)
     req[2] |-> req_gnt_0clock_seq;
endproperty

property master_prop;
  @ (posedge clk)
  disable iff (reset)
     req[0] |-> master_seq;
endproperty
  
//=================================================
// Assertion Directive Layer
//=================================================
req_gnt_1clock_assert    : assert property (req_gnt_1clock_prop);
req_gnt_3to5clock_assert : assert property (req_gnt_3to5clock_prop);
req_gnt_0clock_assert    : assert property (req_gnt_0clock_prop);
master_assert            : assert property (master_prop);

//=================================================
// Drive the input vectors to test assetion
//=================================================
initial begin
  // Init all the values
  reset  <= 0;
  for (int i = 0; i < 3; i++) begin
    req[i] <= 0;
    gnt[i] <= 0;
  end
  @ (posedge clk);
  req[0] <= 1;
  @ (posedge clk);
  gnt[0] <= 1;
  req[0] <= 0;
  @ (posedge clk);
  gnt[0] <= 0;
  req[1] <= 1;
  @ (posedge clk);
  req[1] <= 0;
  repeat(3) @ (posedge clk);
  gnt[1] <= 1;
  @ (posedge clk);
  gnt[1] <= 0;
  req[2] <= 1;
  gnt[2] <= 1;
  @ (posedge clk);
  req[2] <= 0;
  gnt[2] <= 0;
  // Cause assertion to fail
  @ (posedge clk);
  req[0] <= 1;
  repeat(2) @ (posedge clk);
  gnt[0] <= 1;
  req[0] <= 0;
  #30 $finish;
end

endmodule
