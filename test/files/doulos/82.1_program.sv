// Section 82.1: Program

module Design (input clock, input [7:0] data, addr,
               output [7:0] Q);
  /*...*/
endmodule

module testbench;

  logic clock = 0;
  logic [7:0] data, addr, Q;

  Design DUT (.*);
  test test_i (.*);

  // Simulation stops when the program finishes
  initial forever #10 clock = !clock;

  program test (input clock, output logic [7:0] data, addr,
                input [7:0] Q);

    clocking cb @(posedge clock);
      default input #2ns output #5ns;
      output data, addr;
      input Q;
    endclocking

    initial
    begin
      cb.addr <= 8'h00;
      cb.data <= 8'haa;
      /*...*/
    end

  endprogram

endmodule


