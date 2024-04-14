// Section 19.1: Config

module Top(/*...*/);
  /*...*/
  Acc U1(/*...*/);
  Acc U2(/*...*/);
  /*...*/
endmodule

module Acc(/*...*/);
  /*...*/
  Adder A1(/*...*/);
  Adder A2(/*...*/);
/*...*/
endmodule

config MyConfig;              // Simple config
  design MyDesign.Top;
  default liblist MyDesign;
  instance Top.U2 use MyGates.Acc;
endconfig

config MyConfig1;             // Hierarchical config - method 1
  design MyDesign.Top;
  instance Top.U2.A1
    use MyLib.Adder;
endconfig

config MyConfig2;             // Hierarchical config - method 2
  design MyDesign.Top;
  instance Top.U2.A1
    use MyLib.Adder;
  instance Top.U1.A2
    use MyGates.CarrySelectAdder : config;
endconfig

config CarrySelectAdder;
  design MyGates.CarrySelectAdder;
  /*...*/
endconfig


