// Section 51.1: Import

import MyPackage::*;
import MyOtherPackage::AName;

package P;
  typedef enum {ON, OFF} stateT;
endpackage : P

module M
  import P::*;                      // imports stateT, and its literals
 (input logic Clock, input logic Reset, output logic O,
  output stateT s);
endmodule


