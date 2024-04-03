// Section 80.5: Procedural Assignment

// Assert Reset for one clock period on the fifth negative edge of Clock.
initial
begin
  Reset = repeat(5) @(negedge Clock) 1;
  Reset = @(negedge Clock) 0;
end


