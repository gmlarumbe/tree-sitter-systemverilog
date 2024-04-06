// Section 76.6: Parameter

// Type Parameter
module M1 #(int BitNo = 7, 
            localparam P = BitNo*4, // P depends on BitNo
            parameter type ParType = shortreal) 
           (input bit [BitNo:0] In,
            output bit [BitNo:0] Out);
			
  ParType P = 0; // Type of P is set by ParType parameter
                 //(shortreal unless redefined)
  /*...*/
endmodule

module M2;
  bit [15:0] In, Out;
  M1 #(.BitNo(15), .ParType(real)) U1 (In, Out);  
                 // ParType redefined as real
endmodule


