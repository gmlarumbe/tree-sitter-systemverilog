// Section 105.3: Timing Control

// Assert Reset for one clock period on the fifth negative edge of Clock.
initial begin
  Reset = repeat(5) @(negedge Clock) 1;
  Reset = @(negedge Clock) 0;
end


