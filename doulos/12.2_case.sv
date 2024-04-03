// Section 12.2: Case

casez ({A, B, C, D, E[3:0]})
  8'b1??????? : Op <= 2'b00;
  8'b010????? : Op <= 2'b01;
  8'b001???00 : Op <= 2'b10;
  default :     Op <= 2'bxx;
endcase


