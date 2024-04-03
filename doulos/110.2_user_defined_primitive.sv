// Section 110.2: User Defined Primitive

primitive Latch (Q, D, Ena);
  output Q;
  input D, Ena;

  reg Q;                             // Level sensitive UDP

  table
//  D Ena : old Q : Q
    0 0   :   ?   : 0;
    1 0   :   ?   : 1;
    ? 1   :   ?   : -;               // Keeps previous value
    0 ?   :   0   : 0;
    1 ?   :   1   : 1;
  endtable

endprimitive


