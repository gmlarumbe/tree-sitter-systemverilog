// Section 27.1: Defparam

module LayoutDelays;
  defparam Design.U1.T_f = 2.7;
  defparam Design.U2.T_f = 3.1;
  /*...*/
endmodule

module Design (/*...*/);
  /*...*/
  and_gate U1 (f, a, b);
  and_gate U2 (f, a, b);
  /*...*/
endmodule

module and_gate (f, a, b);
  output f;
  input a, b;
  parameter T_f = 2;
  and #(T_f) (f,a,b);
endmodule


