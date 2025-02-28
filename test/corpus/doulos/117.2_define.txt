// Section 117.2: `define

// Text macro with arguments
`define nand(delay) nand #(delay)

`nand(3) (f,a,b);
`nand(4) (g,f,c);


