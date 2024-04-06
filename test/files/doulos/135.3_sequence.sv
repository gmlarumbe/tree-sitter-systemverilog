// Section 135.3: Sequence

// first_match
sequence s1;
  (a ##[1:2] b) or (c ##[2:4] d);
endsequence

sequence s2;
  first_match(s1);
  // s2 results in the earlier match from one of the following:
  // a ##1 b
  // a ##2 b
  // c ##2 d // Ending at the same time with previous. If both match, 
             // first_match results in two sequences.
  // c ##3 d
  // c ##4 d
endsequence


