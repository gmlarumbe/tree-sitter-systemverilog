// Section 33.1: Event

event StartClock, StopClock;

always
fork
  begin : ClockGenerator
    Clock = 0;
    @StartClock forever
      #HalfPeriod Clock = !Clock;
  end
  @StopClock disable ClockGenerator;
join

initial
begin : stimulus
  /*...*/
  -> StartClock;
  /*...*/
  -> StopClock;
  /*...*/
  -> StartClock;
  /*...*/
  -> StopClock;
end


