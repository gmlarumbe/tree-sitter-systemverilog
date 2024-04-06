// Section 110.3: User Defined Primitive

primitive DFF (Q, Clk, D);
  output Q;
  input Clk, D;

  reg Q;                             // Edge sensitive UDP

  initial
    Q = 1;

  table
//  Clk  D  : old Q : Q
     r   0  :   ?   : 0;      // Clock '0'
     r   1  :   ?   : 1;      // Clock '1'
    (0?) 0  :   0   : -;      // Possible Clock
    (0?) 1  :   1   : -;      //    "           "
    (?1) 0  :   0   : -;      //    "           "
    (?1) 1  :   1   : -;      //    "           "
    (?0) ?  :   ?   : -;      // Ignore falling clock
    (1?) ?  :   ?   : -;      //   "   "    "
     ?   *  :   ?   : -;      // Ignore D changes on steady clock
  endtable

endprimitive


