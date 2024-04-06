// Section 89.1: Repeat

initial
begin
  Clock = 0;
  repeat (MaxClockCycles)
  begin
    #10 Clock = 1;
    #10 Clock = 0;
  end
end


