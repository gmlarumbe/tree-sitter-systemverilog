// Section 36.1: Expression

initial begin
x = A + B;
x = !A;
x = (A && B) || C;
x = A[7:0];
x = B[1];
x = -4'd12/3;               // A large positive number
x = "Hello" != "Goodbye";   // This is true (1)
x = $realtobits(r);        // System function call
x = {A, B, C[1:6]};          // Concatenation (8 bits)
x = (1:2:3);                  // MinTypMax
end

