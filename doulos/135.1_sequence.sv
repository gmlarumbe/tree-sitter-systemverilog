// Section 135.1: Sequence

property p;
a ##N b;    // a must be true on the current clock tick, and b on the Nth
            // clock tick after a is true
endproperty

property p;
a ##[2:5] b // a must be true on the current clock tick, and b must be true
            // on some clock tick between 2 and 5 after a is true
endproperty

sequence s1;
  a ##1 b;
endsequence

sequence s2;
  @(posedge clk2)
  // Reference s1 in s2. s1 starts one clock cycle after the occurrence
  // of d in sequence s2
  c ##1 d ##1 s1 ##1 f;   // Equivalent to c ##1 d ##1 a ##1 b ##1 f;
endsequence

sequence s3;
  // Use ended method in s2. Now  s1 must end successfully one clock tick
  // after d
  c ##1 d ##1 s1.ended ##1 f;
endsequence


