// Section 57.5: Interface

// Using parameters in interfaces:
interface FPGAtoDSPInt #(AddrWidth = 8, DWidth = 8) (input logic Clk);
  /*...*/
  logic [AddrWidth-1:0] addr;
  logic [DWidth-1:0] data;
  modport Slave( /*...*/
                import task AddrGen());
  modport Master(/*...*/
     import task DInGen(input logic[DWidth-1:0] DIn));

  task DInGen(input logic[DWidth-1:0] DIn);
    /*...*/
  endtask
  task AddrGen;
    /*...*/
  endtask
endinterface: FPGAtoDSPInt

module FPGA(interface GI);
  /*...*/
  initial begin
  if (GI.Start == 0)
    GI.AddrGen;
  end
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
  FPGAtoDSPInt Intf(Clk);     // Instantiate default interface
  FPGAtoDSPInt #(.DWidth(16)) DIntf(clk);  // Changed data bus width
  FPGA FPGAMod(Intf.Slave);   // Access only to AddrGen task
  DSP DSPMod(Intf.Master);    // Access only to DInGen task
  DSP DSPMod1(DIntf.Master);  // 16-bit wide data bus
endmodule


