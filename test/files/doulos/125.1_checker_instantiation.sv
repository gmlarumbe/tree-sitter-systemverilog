// Section 125.1: Checker Instantiation

checker c1(event clk, logic s);
   p1: assert property (@clk s);
endchecker: c1

checker c2(event clk, logic s);
  c1 c1Inst (clk, s);  // static
  always @(clk) begin
    c1 c1_procedural(clk, s); // procedural
  end
endchecker: c2

module m (logic clk, logic a);
  always @(posedge clk) begin
    c2 c2_proc(posedge clk, a); // procedural
  end
endmodule : m


