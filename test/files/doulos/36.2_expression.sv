// Section 36.2: Expression

logic [7:0] Byte7_to_0;
logic [0:7] Byte0_to_7;

module foo (shift, operand, result);
input [4:0] shift;
input [31:0] operand;
output [7:0] result;

initial begin
Byte7_to_0[2 +: 3]++;                   // Same as Byte7_to_0[4:2]
Byte0_to_7[2 +: 3]++;                   // Same as Byte0_to_7[2:4]
Byte7_to_0[6 -: 3]++;                   // Same as Byte7_to_0[6:4]
Byte0_to_7[6 -: 3]++;                   // Same as Byte0_to_7[4:6]
end

assign result = operand[shift -: 8];
endmodule

