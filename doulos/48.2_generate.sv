// Section 48.2: Generate

module FF #(parameter ClkPolarity = 1)
  (input Clk, D, output logic Q);

  if (ClkPolarity)                     // generate is not needed
    always @(posedge Clk) 
      Q <= D;
  else
    always @(negedge Clk) 
      Q <= D;
endmodule


