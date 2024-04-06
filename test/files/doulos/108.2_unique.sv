// Section 108.2: Unique
  
unique casez(S)
  2'b01: State = State1;
  2'b10: State = State2; // 2'b00 and 2'b11 cause a run-time warning
endcase


