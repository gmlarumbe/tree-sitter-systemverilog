// Section 135.2: Sequence

// Consecutive repetition
sequence s1;
    a ##1 b ##1 b ##1 b ##1 c;
endsequence

// Equivalent to:
sequence s2;
    a ##1 b [*3] ##1 c;
endsequence


sequence s3;
    a [*3];                // Equiv. to a ##1 a ##1 a
endsequence


sequence s4;
    (a[*0:2] ##1 b ##1 c);
endsequence


// Equivalent to:
sequence s5;
    (b ##1 c) or (a ##1 b ##1 c) or (a ##1 a ##1 b ##1 c);
endsequence


// Goto repetition
sequence s6;
    a ##1 b[->1:9] ##1 c; // a followed by at most 9 occurrences of b,
                         // followed by c
endsequence


// Non-consecutive repetition
sequence s7;
    a ##1 b [=1:9] ##1 c;
endsequence


// Equivalent to:
sequence s8;
    a ##1 ((!b [*0:$] ##1 b)) [*1:9] ##1 !b[*0:$] ##1 c;
endsequence



