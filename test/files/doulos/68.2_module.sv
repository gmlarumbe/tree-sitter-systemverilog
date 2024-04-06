// Section 68.2: Module

module PYTHAGORAS (X, Y, Z);
  input  [63:0] X, Y;
  output [63:0] Z;

  parameter Epsilon = 1.0E-6;
  real RX, RY, X2Y2, A, B;

  always @(X or Y)
  begin
    RX = $bitstoreal(X);
    RY = $bitstoreal(Y);
    X2Y2 = (RX * RX) + (RY * RY);
    B = X2Y2;
    A = 0.0;
    while ((A - B) > Epsilon || (A - B) < -Epsilon)
    begin
      A = B;
      B = (A + X2Y2 / A) / 2.0;
    end
  end
  assign Z = $realtobits(A);
endmodule


