// Section 67.6: Modports

// Clocking blocks and modports
interface An_Interf(input bit clk);
  wire a, b;
  clocking CB @(posedge clk);
    input a;
    output b;
    /*...*/
  endclocking
 
  modport CTB (clocking CB); // Synchronous testbench modport
  modport TB ( input a, output b);  // Asynchronous tb modport
endinterface

module T (An_Interf.CTB T1); // Testbench with synchronous port
  initial begin
    T1.CB.b <= 1;
    /*...*/
  end
endmodule


