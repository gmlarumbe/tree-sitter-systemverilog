// Section 87.1: Randcase

bit a, b;
randcase         // self-determined precision of each weight expression
   a+b: x =  8;  // 1-bit precision
     5: x =  3;  // 3-bit precision (3'b101)
  4'h9: x = 10;  // 4-bit precision
                 // Weight selection: unsigned 4-bit sum comparison
endcase

  
