// Section 110.1: User Defined Primitive

primitive Mux2to1 (f, a, b, sel);   // Combinational UDP
  output f;
  input a, b, sel;

  table
//  a b sel : f
    0 ?  0  : 0;
    1 ?  0  : 1;
    ? 0  1  : 0;
    ? 1  1  : 1;
    0 0  ?  : 0;
    1 1  ?  : 1;
  endtable

endprimitive


