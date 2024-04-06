// Section 135.6: Sequence

// Multi-clock sequences:
sequence s1;
  @(posedge clk1) a ##1 b;          // Single clock sequence
endsequence

sequence s2;                        // Multiple clock sequence
  @(posedge clk2) c ##1 d ##1 @(posedge clk1) s1;
endsequence

sequence s3;  // Source sequence s1 evaluated on clk1; Destination
              // sequence s3 is evaluated at clk3
  @(posedge clk3) g ##1 h ##1 s1.matched [->1] ##1 k;
endsequence


