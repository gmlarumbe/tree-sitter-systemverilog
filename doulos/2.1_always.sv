// Section 2.1: Always

always @(A or B or C or D) // Equiv. to @(*), @*, or @(A, B, C, D)
begin
  R = {A, B, C, D};
  F = 0;

  for (int I = 0; I < 4; I = I + 1)
    if (R[I])
    begin
      F = I;
      break;
    end
end


