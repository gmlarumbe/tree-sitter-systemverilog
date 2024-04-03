// Section 132.1: Or (sequence operator)

// Sequence with or where one of the operands is a sequence
assert property ( (sig1 ##1 sig2) or sig3 |=> sig4 );

// The property holds if either of these sequences occur:
sig1 ##1 sig2  |=> sig4
// or
sig3 |=> sig4


