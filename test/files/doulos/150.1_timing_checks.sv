// Section 150.1: Timing Checks

reg Err, FastClock;          // Notifier variables

specify
  specparam Tsetup = 3.5, Thold = 1.5,
            Trecover = 2.0, Tskew = 2.0,
            Tpulse = 10.5, Tspike = 0.5,
            Tremoval = 1.5;

  $hold(posedge Clk, Data, Thold);
  $nochange(posedge Clock, Data, 0, 0 );
  $period(posedge Clk, 20, FastClock);
  $recovery(posedge Clk, Rst, Trecover);
  $setup(Data, posedge Clk, Tsetup);
  $setuphold(posedge Clk &&& !Reset, Data,
             Tsetup, Thold, Err);
  $skew(posedge Clk1, posedge Clk2, Tskew);
  $width(negedge Clk, Tpulse, Tspike);

  $removal(posedge Clear, posedge Clk, Tremoval);
  $recovery(posedge Clear, posedge Clk, Trecover);
  // Equivalent to the previous two lines
  $recrem(posedge Clear, posedge Clk, Trecover, Tremoval);

  $timeskew(posedge Rst &&& Clk1, negedge Clk2, 50);
  $fullskew(posedge Rst &&& Clk1, negedge Clk2, 50, 70);
endspecify

