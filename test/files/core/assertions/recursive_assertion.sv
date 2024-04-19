//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module recursive_assertion();
logic clk = 0;
logic req;
//=================================================
// Property Specification Layer
//=================================================
property recursive_prop(M);
      M and (1'b1 |=> recursive_prop(M));
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
recursive_assert : assert property (recursive_prop(req));
//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Assertion testing code
//+++++++++++++++++++++++++++++++++++++++++++++++++
always #1 clk ++;

initial begin
  // Make the assertion pass
  #100 @ (posedge clk) req  <= 1;
  repeat (20) @ (posedge clk);
  req <= 0;
  #10 $finish;
end

endmodule
