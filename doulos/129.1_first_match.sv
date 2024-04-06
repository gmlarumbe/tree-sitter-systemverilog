// Section 129.1: First_match

// Sequence with variable delay
sequence seq1;
  e1 ## [2:5] e2;
endsequence

// e1 and e2 are expressions. Each attempt of sequence seq1 can result in
// matches for up to four of the following sequences:
// e1 ##2 e2
// e1 ##3 e2
// e1 ##4 e2
// e1 ##5 e2

sequence seq1;
    e1 ##2 e2;
endsequence

sequence seq1;
    e1 ##3 e2;
endsequence

sequence seq1;
    e1 ##4 e2
endsequence

sequence seq1;
    e1 ##5 e2
endsequence


// However, the following sequence seq_first can result in a match for only one
// of the above four sequences.
sequence seq_first;
  first_match(e1 ## [2:5] e2);
endsequence

// Whichever match of the above four sequences ends first is a match of sequence seq_first.


