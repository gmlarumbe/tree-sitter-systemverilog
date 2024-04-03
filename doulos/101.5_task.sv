// Section 101.5: Task

// Tasks in interfaces
interface A (input logic Clk);
  logic Start;
  /*...*/
  task Task1;
    /*...*/
  endtask: Task1
endinterface: A
module Mod(A Interf);
  /*...*/
always @(Interf.Start)
    Interf.Task1;
endmodule
module DUT;
  logic Clk;
  A Intf(Clk);                  // Interface instantiation
  Mod U1(.Interf(Intf.Task1));  // Only has access to the
                                // Task1 task
  /*...*/
endmodule


