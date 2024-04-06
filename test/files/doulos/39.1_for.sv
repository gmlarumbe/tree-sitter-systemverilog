// Section 39.1: For

V = 0;
for (int I = 0, int J = 3; I < 4; I++, J--)
begin
  F[I] = A[I] & B[J];        // 4 separate and gates
  V = V ^ A[I];              // 4 cascaded xor gates
end


