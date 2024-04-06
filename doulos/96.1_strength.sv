// Section 96.1: Strength

module foo;
assign (weak1, weak0) f = a + b;
trireg (large) c1, c2;
and (strong1, weak0) u1 (x, y, z);
endmodule

