// Section 53.1: Initial

// Generate vectors in a testbench
logic Clock, Enable, Load, Reset;
logic [7:0] Data;
parameter HalfPeriod = 5;

initial
begin : ClockGenerator
  Clock = 0;
  forever
    #(HalfPeriod) Clock = !Clock;
end

initial
begin
       Load = 0;
       Enable = 0;
       Reset = 0;
  #20  Reset = 1;
  #100 Enable = 1;
  #100 Data = 8'haa;
       Load = 1;
  #10  Load = 0;
  #500 disable ClockGenerator;   // Stops clock generator
end


