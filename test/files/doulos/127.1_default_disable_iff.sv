// Section 127.1: default disable iff

module m;
  default disable iff rst;
  /*...*/
  // inherits disable iff rst from enclosing module
  checker Check1 (logic sig, event clk = $inferred_clock);
    default clocking @clk;
    endclocking;

    property p1(logic psig);
        a |-> b;
        /*...*/
    endproperty : p1

    assert1: assert property (p1(.psig(test_sig)));
  endchecker: Check1
endmodule : m


