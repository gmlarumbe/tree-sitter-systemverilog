module m;
    default clocking @clk1; endclocking
    default disable iff rst1;
    checker c1;
        // Inherits @clk1 and rst1
        // ...
    endchecker : c1
    checker c2;
        // Explicitly redefines its default values
        default clocking @clk2; endclocking
        default disable iff rst2;
        // ...
    endchecker : c2
    // ...
endmodule : m
