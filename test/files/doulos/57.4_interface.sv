// Section 57.4: Interface

// Multiple tasks exports using forkjoin:
interface FPGAtoDSPInt (input logic clk);
  /*...*/
  // Tasks executed concurrently as a fork-join block
  extern forkjoin task do_Reg( );
  extern forkjoin task AddrGen(input logic[7:0] Addr);
  modport Slave(input A, output B,  /*...*/
                export task AddrGen()); // Export from module
                                        // using modport
  modport Master(output B, input A, /*...*/
               import task AddrGen(input logic[7:0] Addr));
                          // Import requires the full task prototype
  initial  do_Reg;
endinterface: FPGAtoDSPInt;

module FPGA(interface GI);
  task GI.do_Reg;
  /*...*/
  endtask
  task GI.AddrGen;
    /*...*/
  endtask
endmodule

module DSP(interface GI);
  logic [7:0] Addr;
  always @(posedge GI.Clk)
    GI.AddrGen(Addr);         // Call slave method via the interface
  /*...*/
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);
  FPGA FPGAMod1(Intf.Slave);  // Exports do_Reg and AddrGen task
  FPGA FPGAMod2(Intf.Slave);  // Exports do_Reg and AddrGen task
  DSP DSPMod(Intf.Master);    // Imports AddrGen task
endmodule


