// Section 130.1: Implication

property p;
    s1 |-> s2;
endproperty
// In the example above, if the sequence s1 matches, then sequence s2 must also match.
// If sequence s1 does not match, then the result is true.

property p;
    s1 |=> s2;
endproperty
// The expression above is equivalent to:

`define true 1
property p;
    s1 ##1 `true |-> s2;
endproperty
// where `true is a boolean expression, used for visual clarity, that always evaluates to true.


