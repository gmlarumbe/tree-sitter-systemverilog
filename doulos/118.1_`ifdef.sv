// Section 118.1: `ifdef

`define primitiveModel

module Test1;
/*...*/
`ifdef primitiveModel
  MyDesign_primitives UUT (/*...*/);
`else
  MyDesign_RTL UUT (/*...*/);
`endif
endmodule


