// Section 133.3: Property

// Multi-clock property examples:
sequence s1;
  @(posedge clk1) a ##1 b; // Single clock sequence
endsequence

sequence s2;
  @(posedge clk2) c ##1 d; // Single clock sequence
endsequence

sequence MultSeq;          // Multiple clock sequence
  @(posedge clk1) e ##1 @(posedge clk2) s1 ##1
  @(posedge clk3) s2; 
endsequence

property p1;       // Property with a named multiple-clock seq. 
  MultSeq;
endproperty

property p2;       // Property with multiple-clock implication
  @(posedge clk1) a ##1
  @(posedge clk2) s1 |=> @(posedge clk3) s2;
endproperty

property mult_p6;  // Property with implication with named
  MultSeq |=> MultSeq;      // Multi-clocked sequences
endproperty

property p3;      // a, b, cond, e are clocked on posedge clk1
  @(posedge clk1) a ##1 b |-> 
  if (cond)
    (1 |=> @(posedge clk2) d)
  else
    e ##1 @(posedge clk3) f;  
endproperty      


