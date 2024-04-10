module mod (clk, reset_n, inp, a, b);

input clk;
input clk0, clk1;
input [W-1:0] inp;
output [3:0] a, b;
output foo, bar;
output baz;
input mytype bus1;
output mytype bus2;

endmodule
