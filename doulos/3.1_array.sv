// Section 3.1: Array

wire  [7:0] A [0:15][0:15], B[0:15][0:15];  // Two 16x16 array of bytes
A[0][1][2] = B[1][2][3];     // Bit-select

A = B;

logic [15:0] Array1;
logic [7:0] Array2;
Array2 = Array1[8:1];        // Part-select

int A [7:0];
int B [31:0];
assign A = B[7:0];        // B[7:0] is also an unpacked aray


