// Section 45.4: Function

module decoder (A, Y);
  parameter NumOuts = 16;
  localparam NumIns = BitsToFit (NumOuts); 
  input [NumIns-1:0] A;
  function integer BitsToFit(integer n);
    /*...*/                            // Depends only on constants
  endfunction
  /*...*/
endmodule


