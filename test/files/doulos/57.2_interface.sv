// Section 57.2: Interface

// Using generic interface:
module FPGA1 (interface Interf, input logic Clk);
  /*...*/
endmodule

module DSP1(interface Interf, input logic Clk);
  /*...*/
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf();            // Instantiate the interface
  FPGA1 FPGAMod(.Interf(Intf), .Clk(Clk));
  DSP1 DSPMod(.*, .Interf(Intf)); // Partial implicit port connection
endmodule


