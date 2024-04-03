// Section 79.2: Priority

priority casez(S)
  2'b01:   State = State1;
  2'b10:   State = State2;
  default: State = Idle;
endcase


