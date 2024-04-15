// Section 77.1: PATHPULSE$

module foo;
specify
  (clk => q) = 1.2;
  (rst => q) = 0.8;
  specparam PATHPULSE$clk$q = (0.5,1),
            PATHPULSE$ = (0.5);
endspecify
endmodule

