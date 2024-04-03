// Section 91.1: Specify

module M (F, G, Q, Qb, W, A, B, D, V, Clk, Rst, X, Z);
  input A, B, D, Clk, Rst, X;
  input [7:0] V;
  output F, G, Q, Qb, Z;
  output [7:0] W;
  reg C, Err;
// Functional Description /*...*/
  specify
    specparam TLH$Clk$Q    = 3,
              THL$Clk$Q    = 4,
              TLH$Clk$Qb   = 4,
              THL$Clk$Qb   = 5,
              Tsetup$Clk$D = 2.0,
              Thold$Clk$D  = 1.0;
// Simple path, full connection
    (A, B *> F) = (1.2:2.3:3.1, 1.4:2.0:3.2);
// Simple path, parallel connection, positive polarity
    (V + => W) = 3,4,5;
// Edge-sensitive paths, with polarity
    (posedge Clk *> (Q  +: D)) = (TLH$Clk$Q,THL$Clk$Q);
    (posedge Clk *> (Qb -: D)) = (TLH$Clk$Qb,THL$Clk$Qb);
// State dependent paths
    if (C) (X *> Z) = 5;
    if (!C && V == 8'hff) (X *> Z) = 4;
    ifnone (X *> Z) = 6;	// Default SDPD, X to Z
// Timing checks
    $setuphold(posedge Clk, D,
               Tsetup$Clk$D, Thold$Clk$D, Err);
  endspecify
endmodule


