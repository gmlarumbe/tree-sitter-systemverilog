module assertion_boolean();

wire ce, en;
wire [7:0] addr;

// This code will not compile
// (en && ce && addr < 100);

// INFO: Added sequence to make it compile
sequence s;
  (en && ce && addr < 100);
endsequence


endmodule
