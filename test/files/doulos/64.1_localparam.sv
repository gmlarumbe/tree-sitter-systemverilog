// Section 64.1: Localparam

module Decoder (A, Y);
  parameter NumIns = 3;
  localparam NumOuts = 2 ** NumIns;
  input [NumIns -1 : 0] A;
  output[NumOuts-1 : 0] Y;
/*...*/
endmodule


