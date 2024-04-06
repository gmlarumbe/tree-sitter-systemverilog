// Section 13.1: Casting

typedef struct {
  bit A;
  union packed {int i; bit[31:0] f;} B; 
} Struct1;

typedef bit [$bits(Struct1) - 1 : 0] C_Type; 

Struct1 S[7:0];             // Unpacked array of structures
C_Type C = C_Type'(S[1]);   // Convert structure to array of bits
S[2] = Struct1'(C);         // Convert array of bits back to structure


