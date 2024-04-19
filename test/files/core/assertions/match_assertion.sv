//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module match_assertion();

logic clk = 0;
always #1 clk ++;

logic burst_enable, master_busy, slave_busy;
//=================================================
// Property Specification Layer
//=================================================
property first_match_prop;
  @ (posedge clk) 
    $rose(burst_enable) |=> 
      first_match(burst_enable ##[0:4] !master_busy);
endproperty
       
property throughout_prop;
  @ (posedge clk) 
    $rose(burst_enable) |-> 
      (burst_enable) throughout 
          ( ##2 (!slave_busy && !master_busy) [*6]);
endproperty

property within_prop;
  @ (posedge clk) 
    $rose(burst_enable) |=> 
       (!slave_busy[*6]) within 
           (($fell(master_busy)) ##1 !master_busy[*7]);
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
within_assert     : assert property (within_prop);
throughout_assert : assert property (throughout_prop);
first_match_assert: assert property (first_match_prop);
//=================================================
// Generate input vectors
//=================================================
initial begin
  burst_enable <= 0; master_busy <= 1; slave_busy <= 1;
  @ (posedge clk); 
  burst_enable <= 1;
  @ (posedge clk); 
  master_busy <= 0;
  @ (posedge clk); 
  slave_busy <= 0;
  repeat(6) @ (posedge clk);
  slave_busy <= 1;
  @ (posedge clk); 
  burst_enable <= 0;
  master_busy <= 1;
  // Fail both the assertion
  repeat(20) @ (posedge clk);
  burst_enable <= 0; master_busy <= 1; slave_busy <= 1;
  @ (posedge clk); 
  burst_enable <= 1;
  @ (posedge clk); 
  master_busy <= 0;
  @ (posedge clk); 
  slave_busy <= 0;
  repeat(5) @ (posedge clk);
  slave_busy <= 1;
  @ (posedge clk); 
  burst_enable <= 0;
  master_busy <= 1;
  // Terminate the sim
  repeat(20) @ (posedge clk);
  $finish;
end

endmodule
