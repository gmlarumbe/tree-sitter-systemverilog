// Section 54.1: Inside

// Given
logic IsAMember;
logic [1:0] a;
IsAMember = a inside {2'b01, 2'b10};

// then
initial begin
a = 2'b00;                      // Result = 1'b0
a = 2'b01;                      // Result = 1'b1
a = 2'b10;                      // Result = 1'b1
a = 2'b11;                      // Result = 1'b0
a = 2'b0x;                      // Result = 1'bx
a = 2'b1x;                      // Result = 1'bx
a = 2'bz0;                      // Result = 1'bx
a = 2'bz1;                      // Result = 1'bx
end

