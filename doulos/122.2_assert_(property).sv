// Section 122.2: Assert (Property)

// Module Flipflop above is equivalent to
module FlipFlop (input logic clk, D, output logic Q);
  property P2;
    int d;
    (1,d=D) |-> ##1 (Q == d);
  endproperty

  always @(posedge clk)
  begin
    Label2: assert property (P2);
    Q <= D;
  end
endmodule


