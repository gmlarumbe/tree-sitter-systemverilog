// Section 110.4: User Defined Primitive

primitive SRFF (output reg Q = 1'b1, input S, R);
//  initial Q = 1'b1;
  table
 // S R   Q   Q+
    1 0 : ? : 1 ;
    f 0 : 1 : - ;
    0 r : ? : 0 ;
    0 f : 0 : - ;
    1 1 : ? : 0 ;
  endtable
endprimitive


