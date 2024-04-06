// Section 80.1: Procedural Assignment

always @(Inputs)
begin : CountOnes
  integer I;
  f = 0;
  for (I=0; I<8; I=I+1)
    if (Inputs[I])
      f = f + 1;
end


