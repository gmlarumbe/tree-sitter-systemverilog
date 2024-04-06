// Section 48.1: Generate

module TriStateSelector #(parameter N = 4)
  (input [N-1:0] D, E,
   output Y);
  
  generate
    genvar I;
    for (I=0; I<N; I=I+1) begin: B
      assign Y = E[I] ? D[I] : 1'bz;
    end
  endgenerate
endmodule


