// Section 57.1: Interface

// Using named bundle:
interface FPGAtoDSPInt;               // Interface definition
  logic Start, N_Reset;
  logic N_CS, N_DS, R_NW;
  logic [7:0] AddrBus, DataBus;
  /*...*/
endinterface: FPGAtoDSPInt

module FPGA (FPGAtoDSPInt Interf, input logic Clk);
  /*...*/
endmodule

module DSP (FPGAtoDSPInt Interf, input logic Clk);
  /*...*/
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Interf();
  FPGA FPGAMod(Interf, Clk);          // Positional connection
  DSP DSPMod(.Interf(Interf), .Clk); // Named and .name
/* or
  FPGA FPGAMod (.*);              // Implicit port connections
  DSP DSPMod (.*);
*/
endmodule


