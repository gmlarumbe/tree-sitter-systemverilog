// Section 92.1: Specparam

specify
  specparam tRise$a$f = 1.0,
            tFall$a$f = 1.0,
            tRise$b$f = 1.0,
            tFall$b$f = 1.0;
  (a *> f) = (tRise$a$f, tFall$a$f);
  (b *> f) = (tRise$b$f, tFall$b$f);
endspecify

module (input I1, I2, output O1);
  specparam Spec = 1.0;
  parameter Par = 1;
  /*...*/
endmodule


