// Section 109.1: Unpacked Array Concatenation

int A[1:4] = '{1,2,3,45};     // assignment pattern
int B[4]   = {1,2,3,4};       // unpacked array concatenation
int C[1:8] = {A, 1,2,3,4};    // legal
int D[1:8] = '{A, 1,2,3,4};   // illegal
// int E[1:8] = {default:0};     // illegal
int F[1:8] = '{default:0};    // legal


