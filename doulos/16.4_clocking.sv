// Section 16.4: Clocking

//Multiple clocking blocks:
interface I1 (input bit clock1);  /*...*/ endinterface
interface I2 (input bit clock2);  /*...*/ endinterface

module tf(I1 A, I2 B);
  clocking cb1 @(posedge A.clock1);
    default input #2 output #5;
    // input A.address; // INFO: Not supported by most tools
    input address = A.address;
    output data = A.data;
  endclocking

  clocking cb2 @(posedge B.clock2);
    default input #1 output #1;
    output start = B.start, size = B.size;
  endclocking

  initial begin : Test
    cb1.data <= 1;
    /*...*/
  end

  module CtrlMod;
    default clocking cb1; // Clocking block cb1 set as default
                          // inside CtrlMod module
    initial begin
        if (cb1.data == 1)
        ## 10;            // Delays execution by 10 cycles using the
                          // default clocking (A.clock1)
        /*...*/
    end
  endmodule
endmodule


