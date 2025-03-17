`define MACRO1(a=5,b="B",c) initial $display(a,,b,,c);
`define MACRO2(a=5, b, c="C") initial $display(a,,b,,c);
