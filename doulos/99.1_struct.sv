// Section 99.1: Struct

typedef struct {
  int A;
  union {bit i; byte j;} B;
} Struct1;                    // Named structure
Struct1 S[7:0];               // Array of structures


