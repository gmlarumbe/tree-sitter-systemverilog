// Section 130.1: Implication

s1 |-> s2;
// In the example above, if the sequence s1 matches, then sequence s2 must also match.
// If sequence s1 does not match, then the result is true.

s1 |=> s2;
// The expression above is equivalent to:

`define true 1
s1 ##1 `true |-> s2;
// where `true is a boolean expression, used for visual clarity, that always evaluates to true.


