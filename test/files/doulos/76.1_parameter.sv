// Section 76.1: Parameter

module Shifter #(NBits = 8)     // Keyword parameter is omitted
  (input Clock, In, Load,
   input [NBits-1:0] Data,
   output Out);

  always @(posedge Clock)
    if (Load)
      ShiftReg <= Data;
    else
      ShiftReg <= {ShiftReg[NBits-2:0], In};

  assign Out = ShiftReg[NBits-1];

endmodule

module TestShifter;
  /*...*/

  defparam U2.NBits = 10;

  Shifter #(16) U1 (/*...*/);            // 16-bit shift register
  Shifter U2 (/*...*/);                   // 10-bit shift register
endmodule


