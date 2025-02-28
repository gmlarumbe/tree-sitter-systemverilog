// Section 118.2: `ifdef

// Chained nested conditional directives
module Test2;
/*...*/
`ifdef Block1
  `ifndef Block2
    initial $display ("Block1 is defined");
  `else
    initial $display ("Block1 and Block2 defined");
  `endif
`elsif Block3
  initial $display ("Block3 defined, Block1 is not");
`else
  initial $display ("Block1, Block3 not defined.");
`endif
endmodule


