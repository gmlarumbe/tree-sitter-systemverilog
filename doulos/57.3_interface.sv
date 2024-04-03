// Section 57.3: Interface

// Interface ports, tasks in interfaces:
interface FPGAtoDSPInt (input logic Clk); 
  logic Start, Int_Sig;
  /*...*/
  task AddrGen;
    /*...*/
  endtask: AddrGen
endinterface: FPGAtoDSPInt

module FPGA(FPGAtoDSPInt Interf); 
  /*...*/  
always @(Interf.Start)
  Interf.AddrGen;  
  /*...*/
  always @(posedge Interf.clk)
    Interf.Addr[0] <= Int_Sig; 
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);             // Instantiate the interface
  FPGA FPGAMod(.Interf(Intf));        // Has access to AddrGen
  /*...*/
endmodule


