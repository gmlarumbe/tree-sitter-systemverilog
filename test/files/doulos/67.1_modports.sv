// Section 67.1: Modports

interface FPGAtoDSPInt;
  logic Start, N_Reset;
  logic N_CS, N_DS, R_NW;
  logic [7:0] AddrBus, DataBus;
  modport Master(output AddrBus, ref DataBus);
  modport Slave (input  AddrBus, ref DataBus);
  /*...*/
endinterface: FPGAtoDSPInt

module FPGA (FPGAtoDSPInt.Master Interf, input logic Clk);  // Modport specified in module header
  /*...*/
endmodule

module DSP (FPGAtoDSPInt Interf, input logic Clk);
  /*...*/
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf;
  FPGA FPGAMod(.Interf(Intf), .Clk);
  DSP DSPMod(.Interf(Intf.Slave), .Clk(Clk));  // Modport specified in port connection
endmodule


