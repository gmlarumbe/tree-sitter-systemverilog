// Section 74.1: Operators

int a = -16'd10;                    // An expression, not a signed number!
int a = a + b;
int a = x % y;
int a = Reset && !Enable;           // Same as Reset && (!Enable)
int a = a && b || c && d;           // Same as (a && b) || (c && d)
int a = ~4'b1101;                   // Gives 4'b0010
int a = &8'hff;                     // Gives 1'b1 (all bits are 1)
reg signed [3:0] ShftIn, ShftOut;
ShftIn = 4'b1010;
ShftOut = (ShftIn >>> 2);  // ShftOut becomes 4'b1110


