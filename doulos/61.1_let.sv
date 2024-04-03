// Section 61.1: Let

package p;
  let aTimesB (int a, int b) = 
              ($bits(a) + $bits(b))'(a * b);
endpackage

module m;
  import p::*;
  int a, b;
  initial begin
     a = 2; b = 3;
     $display( aTimesB(.a(a), .b(b)) );  // 6
  end
endmodule


