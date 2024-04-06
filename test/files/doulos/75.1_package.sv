// Section 75.1: Package

package P0;
  int a;
  const bit c = 0;
endpackage: P0

package P1;
  int b;
  const bit c = 0;
endpackage: P1

module Mod;
  import P0::*;
  wire w1 = P1::b; // no need for import clause
  wire w2 = c;     // The import of P0::c is forced
  import P1::c;    // Error: conflict between P0::c and P1::c
endmodule


