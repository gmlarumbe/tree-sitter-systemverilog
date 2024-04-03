// Section 117.1: `define

`define SUBBLOCK1 subblock1_rtl
`define SUBBLOCK2 subblock2_rtl
`define SUBBLOCK3 subblock3_gates

module TopLevel; /*...*/

  `SUBBLOCK1 sub1_inst (/*...*/);
  `SUBBLOCK2 sub2_inst (/*...*/);
  `SUBBLOCK3 sub3_inst (/*...*/);
  /*...*/
endmodule


