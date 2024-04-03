// Section 135.2: Sequence

// Consecutive repetition
a ##1 b ##1 b ##1 b ##1 c;

// Equivalent to:
a ##1 b [*3] ##1 c; 		

a [*3];	               // Equiv. to a ##1 a ##1 a

(a[*0:2] ##1 b ##1 c);

// Equivalent to:
(b ##1 c) or (a ##1 b ##1 c) or (a ##1 a ##1 b ##1 c);

// Goto repetition
a ##1 b[->1:9] ##1 c // a followed by at most 9 occurrences of b, 
                     // followed by c

// Non-consecutive repetition
a ##1 b [=1:9] ##1 c

// Equivalent to:
a ##1 ((!b [*0:$] ##1 b)) [*1:9]) ##1 !b[*0:$] ##1 c


