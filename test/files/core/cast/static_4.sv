initial begin
    logic [7:0] regA;
    logic signed [7:0] regS;
    regA = unsigned'(-4); // regA = 8'b11111100
    regS = signed'(4'b1100); // regS = -4

    y = const'(x);
end
