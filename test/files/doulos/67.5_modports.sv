// Section 67.5: Modports

// Exporting tasks:
interface FPGAtoDSPInt (input logic Clk);
  /*...*/
  modport Slave(input a,/*...*/
                export task DInGen(input logic[7:0] DIn));
                         // Export from module that uses the modport

  modport Master(output a,/*...*/
                import task DInGen(input logic[7:0] DIn));
endinterface: FPGAtoDSPInt

module FPGA(interface Interf);
  task Interf.DInGen(input logic[7:0] DIn); // DInGen method
    /*...*/
  endtask
endmodule

module DSP(interface GI);
  logic [7:0] DIn;
  always @(posedge GI.Clk)
    GI.DInGen(DIn);         // Call slave method via the interface
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);
  FPGA FPGAMod(Intf.Slave); // Exports DInGen task
  DSP DSPMod(Intf.Master);  // Imports DInGen task
endmodule


