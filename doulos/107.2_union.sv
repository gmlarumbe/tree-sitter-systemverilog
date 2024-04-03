// Section 107.2: Union

typedef struct packed { // Unsigned by default
  bit [ 3:0]  A4;
  bit [ 7:0]  B8;
  bit [15:0] C16;
} Struct1;

typedef union packed {  // Unsigned by default
  Struct1 AStruct;
  bit [27:0]        A28;
  bit [13:0][1:0] A14_2;
} Union1;

Union1 U1;
byte B; 
bit [3:0] Nib;
B = U1.A28[27:26];      // Same as B = U1.A14_2[13];
Nib = U1.A28[27:24];    // Same as Nib = U1.Astruct.A4;


