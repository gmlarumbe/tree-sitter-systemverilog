// Section 68.5: Module

// Extern module
// Given
extern module Counter #(N = 8)
                      (input Clock, Reset,
                       output logic [N-1:0] Count);

module Counter (.*);
  /*...*/
endmodule

// is equivalent to
module Counter #(N = 8) (input Clock, Reset,
                         output logic [N-1:0] Count);
  /*...*/
endmodule


