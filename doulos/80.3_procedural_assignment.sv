// Section 80.3: Procedural Assignment

always @(posedge Clock)
begin
  c <= b;      // Uses the 'old' value of 'b'
  b <= a;
end


