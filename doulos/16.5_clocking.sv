// Section 16.5: Clocking

interface ABus(input logic clk); // Interface with modports
  wire a, b, c, d;
  logic req, gnt;
  clocking cb @(posedge clk);
    input a;
    output b, c;
    inout d;
    property p1; req ##[1:3] gnt; endproperty
  endclocking

  modport DUT (input clk, b, c,// DUT modport
               output a, inout d);
  modport STB (clocking cb);   // Synchronous testbench modport
  modport TB  (input a,        // Asynchronous testbench modport
               output b, c, inout d);
endinterface

module AMod1(ABus.DUT b); 
  /*...*/
endmodule

module TB (ABus.STB b1, ABus.STB b2 ); // 2 synchronous ports
  typedef virtual ABus.STB SYNCTB;
  task ATask(SYNCTB s);
    s.cb.a <= 1;
  endtask
  /*...*/
endmodule

module top;
  logic clk;
  ABus b1(clk);
  ABus b2(clk);
  AMod1 M1(b1);
  TB Test(b1, b2);
  /*...*/
endmodule


