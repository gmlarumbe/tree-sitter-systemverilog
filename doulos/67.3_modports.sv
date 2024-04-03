// Section 67.3: Modports

// Generic Interface:
module FPGA(interface Interf);
  /*...*/
endmodule

module DUT;
  FPGAtoDSPInt Intf;
  FPGA FPGAMod(Intf.Slave);  // Connect modport to module instance
 /*...*/
endmodule


