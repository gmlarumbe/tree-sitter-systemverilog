// Section 108.1: Unique

bit[1:0] S;

unique if(S[1:0] == 2'b01) 
  State = State1;
else if (S[1:0] == 2'b10) 
  State = State2;        // 2'b00 and 2'b11 cause a run-time warning

