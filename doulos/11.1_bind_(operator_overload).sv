// Section 11.1: Bind (Operator Overload)

typedef struct {
  bit  A;
  real B;
} A_Struct;
A_Struct X, Y, Z, Q;

bind + function A_Struct fadds(A_Struct, A_Struct);
bind + function A_Struct faddr(A_Struct, real);
bind + function A_Struct faddi(A_Struct, int);

assign Q = X + 2.0; // Equivalent to Q = faddr (X, 2.0)
assign Y = X + 5;   // Equivalent to Y = faddi (X, 5)
always @(posedge clk) Z += X;   // Equivalent to Z = Z + X,
                                // i.e. Z = fadds (Z, X)


