// Section 1.1: Alias

// Reverse the bits of bi-directional ports
module ReverseBits (inout [7:0] A, B);
  alias A = {B[0],B[1],B[2],B[3],B[4],B[5],B[6],B[7]};
endmodule


