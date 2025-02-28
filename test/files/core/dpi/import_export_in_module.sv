module testbench;
    import "DPI" function string fn1 (input string str1);
    import "DPI-C" function void dpiWriteArray (input bit[7:0] data[]);
    import "DPI-C" pure function void dpiReadArray (output bit[7:0] data[]);
    import "DPI-C" function void dpiAesSetKey ( int key_high_u, int key_high_l,
                                                int key_low_u, int key_low_l );
    import "DPI-C" function void dpiAesSetIV (int iv_high_u, int iv_high_l,
                                              int iv_low_u, int iv_low_l);
    import "DPI-C" function void dpiAesSetSkip (int skip);
    import "DPI-C" function void dpiAesCBCEncrypt ();
endmodule : testbench


module toto (input logic dummy);
    import "DPI-C" pure function real fabs (input real a);
    import "DPI-C" context function real fcons (input real a);
    import "DPI-C" string_sv2c = task stringsv2c();
    import "DPI-C" int_sv2c = task intsv2c();
    import "DPI-C" context int_sv2c = task intsv2cont();
    logic a;
endmodule
