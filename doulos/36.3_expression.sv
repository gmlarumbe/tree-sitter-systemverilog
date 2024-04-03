// Section 36.3: Expression

// Multi-Dimensional Arrays
wire [7:0] A [0:15] [0:15];          // 16x16 array of bytes
assign A[0][0] = 8'b1;               // Element select
assign A[1][5][7:4] = A[5][1][3:0];  // Part-select 
assign W = A[1][2][3];               // Bit-select


