// Section 55.3: Instantiation

module foo;
//In the two following examples, the port QB is unconnected
DFF Ff1 (.Clk(Clk), .D(D), .Q(Q), .QB());
// Equivalent to
DFF Ff1 (.Clk, .D, .Q, .QB());
// or
DFF Ff1 (.*, .QB());
DFF Ff2 (Q,, Clk, D);
endmodule

