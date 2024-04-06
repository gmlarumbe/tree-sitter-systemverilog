// Section 29.1: Disable

// Using disable to break a loop externally:
initial
  begin : Clockgen
    Clock = 0;
    forever
      #(Period/2) Clock = ~Clock;
  end : Clockgen

initial
  begin : Stimulus
    /*...*/
    disable Clockgen;
  end : Stimulus // Stops the clock


