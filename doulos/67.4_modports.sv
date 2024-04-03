// Section 67.4: Modports

// Tasks in modports:
interface FPGAtoDSPInt (input logic Clk);
  /*...*/
  logic [7:0] AddrBus, DataBus;
  modport Slave(input a /*...*/);
  modport Master(output b,/*...*/
     import task DInGen(input logic[7:0] DIn));
  task DInGen(input logic[7:0] DIn);
    /*...*/
  endtask
endinterface: FPGAtoDSPInt

module FPGA(interface GI);   // Generic Interface
  /*...*/
endmodule

module DSP(interface GI);
  logic [7:0] DIn;
  always @(posedge GI.Clk)
    GI.DInGen(DIn);
  /*...*/
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);    // Instantiate default interface
  FPGA FPGAMod(Intf);        // Access to all Master and Slave tasks
  DSP DSPMod(Intf.Master);   // Access only to DInGen task
endmodule


