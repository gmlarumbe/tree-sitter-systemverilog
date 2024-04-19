//+++++++++++++++++++++++++++++++++++++++++++++++++
// DUT With Immediate assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module assert_immediate();

reg  clk, grant, request;
time current_time;

initial begin
  clk = 0;
  grant   = 0;
  request = 0;
  #4 request = 1;
  #4 grant = 1;
  #4 request = 0;
  #4 $finish;
end

always #1 clk = ~clk;
//=================================================
// Assertion used in always block
//=================================================
always @ (posedge clk)
begin
  if (grant == 1) begin
     CHECK_REQ_WHEN_GNT : assert (grant && request) begin
        $display ("Seems to be working as expected");
     end else begin
        current_time = $time;
        #1 $error("assert failed at time %0t", current_time);
     end
  end
end

endmodule
