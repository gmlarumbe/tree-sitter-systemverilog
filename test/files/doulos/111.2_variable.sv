// Section 111.2: Variable

logic [15:0] V;
logic Parity = 0;
always @(V)
  for ( int i = 0; i <= 15; i++ )
    Parity ^= V[i];


