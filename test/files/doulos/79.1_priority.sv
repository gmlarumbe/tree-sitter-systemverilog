// Section 79.1: Priority

bit[1:0] S;

priority if(S[1:0] == 2'b01) 
  State = State1;
else 
  if (S[1:0] == 2'b10) 
    State = State2;
  else 
      State = Idle;     // Covers all other possible values, so no
                        // warning is issued


