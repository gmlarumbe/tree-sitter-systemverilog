// Section 73.1: Number

int a = -253;               // A signed decimal number
int b = 'Haf;               // An unsized hex number
int c = 6'o67;              // A 6 bit octal number
int d = 8'bx;               // An 8 bit unknown number (8'bxxxx_xxxx)
int e = 4'bz1;              // All but the lsb are Z (4'bzzz1)
reg signed [3:0] S4;
S4 = -4;           // 4'b1100
S4 = S4 >>> 1;     // 4'b1110 = -2
S4 = S4 + 2'sb11;  // 4'b1101 = -3


