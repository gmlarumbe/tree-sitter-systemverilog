// Section 56.1: Interconnect

package nettype_pkg;
  nettype real realnet;
endpackage

module top();
  interconnect [0:1] iBus;
  LDriver L1(iBus[0]);
  RDriver R1(iBus[1]);
  RLMod   m1(iBus);
endmodule : top

module LDriver(output wire logic out);
endmodule : LDriver

module RDriver(output nettype_pkg::realnet out);
endmodule : RDriver

module RLMod(input interconnect [0:1] iBus);
  LDriver L1(iBus[0]);
  RDriver R1(iBus[1]);
endmodule : RLMod


