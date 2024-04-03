// Section 5.1: Assert (Immediate)

always @(posedge clk)
  assert (State != Illegal_State)
    else $error ("Illegal state reached");

initial
begin
  assert (A == B);
  assert (C && D) $display("OK - C and D are both true");
  assert (E) else $warning("E is NOT true");
end


