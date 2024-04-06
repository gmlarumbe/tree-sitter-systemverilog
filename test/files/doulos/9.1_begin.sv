// Section 9.1: Begin

initial
begin
  Load = 0;              // Time 0
  Enable = 0;
  Reset = 0;
  #10  Reset = 1;        // Time 10
  #25  Enable = 1;       // Time 35
  #100 Load = 1;         // Time 135
end

initial
begin : AssignInputs
  for (int I = 0; I < 8; I = I + 1)
    #Period {A, B, C} = I;
end : AssignInputs


