// Section 43.1: Fork

initial
fork : stimulus
  #20 Data = 8'hae;
  #40 Data = 8'hxx;  // This is executed last
  Reset = 0;         // This is executed first
  #10 Reset = 1;
join                 // Completes at time 40


