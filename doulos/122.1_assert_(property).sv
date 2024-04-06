// Section 122.1: Assert (Property)

// Concurrent assertions
module FlipFlop (input logic clk, D, output logic Q);
  property P2;
    int d;
    @(posedge clk) (1,d=D) |-> ##1 (Q == d);
  endproperty

  Label2: assert property (P2);

  always @(posedge clk)
    Q <= D;
endmodule


