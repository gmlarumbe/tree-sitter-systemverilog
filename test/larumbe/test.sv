module top();

initial begin
    bit [95:0] d = {<<8{a, b, c}};
    // bit [95:0] d = {<<{a, b, c}};
    // bit [95:0] d = {>>{a, b}};
    d = {>> {a, b}};
    // d = { << 8{a, b, c}};
end



endmodule
