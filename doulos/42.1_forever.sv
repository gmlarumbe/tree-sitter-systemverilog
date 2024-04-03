// Section 42.1: Forever
  
initial
begin : Clocking
  Clock = 0;
  forever
    #10 Clock = !Clock;
end

initial
begin : Stimulus
  /*...*/
  disable Clocking;         // Stops the clock
end


