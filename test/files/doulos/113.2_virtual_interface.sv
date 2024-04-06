// Section 113.2: Virtual Interface

// Clocking blocks in virtual interfaces
interface AnIntf (input logic clk); 
  wire a, b;
  clocking cb @(posedge clk);
    input b;
    output a;
  endclocking
  modport STB (clocking cb); // Synchronous testbench modport
  modport DUT (input b, output a); // Connects to DUT
endinterface

module Device (interface I);
  /*...*/
endmodule

module Test_Device;
  logic clk;

  AnIntf I1 (clk);
  AnIntf I2 (clk);
  Device Device1 (I1.DUT);
  Device Device2 (I2.DUT);
  Tester test (I1.STB, I2.STB);
endmodule : Test_Device

module Tester (AnIntf i1, AnIntf i2);
  typedef virtual interface AnIntf VI;

  task Drive (VI v);
    v.cb.a <= 1;
  endtask : Drive

  function Sample (VI v);
    return v.cb.b;
  endfunction : Sample

  initial
    begin
      Drive(i1);
      Sample(i1);
      Drive(i2);
      Sample(i2);
    end
endmodule : Tester


