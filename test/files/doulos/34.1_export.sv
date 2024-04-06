// Section 34.1: Export

package P;
  int a, b;
endpackage : P

package Q;
  export P::*;  // export *::* also ok
  import P::*;
  int c;
endpackage : Q

module m;
  import Q::*; // P::a, P::b and Q::c are all potentially visible
endmodule

