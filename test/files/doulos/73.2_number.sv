// Section 73.2: Number

// Broken backward compatibility
reg [63:0] W64;
W64 = 64'bz;       // Verilog-1995: 64'h00000000zzzzzzzz
W64 = 'bz;         // Verilog-2001: 64'hzzzzzzzzzzzzzzzz


