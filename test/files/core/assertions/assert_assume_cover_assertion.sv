//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module assert_assume_cover_assertion();
logic clk = 0;
logic req,gnt;
logic ce,wr;
logic [7:0] addr, data;
//=================================================
// Property Specification Layer
//=================================================
property req_gnt_prop;
  @ (posedge clk)
      req |=> gnt;
endproperty
//=================================================
// Check if address falls in range for a write 
// operation
//=================================================
property addr_hit_prop(int min, int max);
  @ (posedge clk)
   (ce & wr) |-> (addr >= min && addr <= max);
endproperty
//=================================================
// Simple DUT with assert
//=================================================
always @ (posedge clk)
begin
   gnt <= req;
   //==============================================
   // Assert inside a always block
   //==============================================
   req_gnt_assert : assert property (req_gnt_prop);
end
//=================================================
// This is how you use "assume"
//=================================================
req_gnt_assume  : assume property (req_gnt_prop);
//=================================================
// This is how you use "assert"
//=================================================
req_gnt_assert2 : assert property (req_gnt_prop);
//=================================================
// This is how you use "cover"
//=================================================
req_gnt_cover   : cover property (req_gnt_prop);
addr_hit_cover  : cover property (addr_hit_prop(1,5));
//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Assertion testing code
//+++++++++++++++++++++++++++++++++++++++++++++++++
always #1 clk ++;

initial begin
  ce <= 0; wr <= 0; addr <= 0; req <= 0; gnt <= 0;
  data <= 0;
  // Make the assertion pass
  @ (posedge clk) req  <= 1;
  @ (posedge gnt);
  for (int i = 0; i < 10; i ++) begin
    @ (posedge clk);
    ce <= 1;
    wr <= 1;
    addr <= i;
    data <= $random;
    @ (posedge clk);
    ce <= 0;
    wr <= 0;
    addr <= 0;
  end
  @ (posedge clk);
  req <= 0;
  // Check 
  #10 $finish;
end

endmodule
