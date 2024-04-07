// Simple checker containing concurrent assertions
checker my_check1 (logic test_sig, event clock);
    default clocking @clock; endclocking
    property p(logic sig);
        // ...
        a |-> b;
    endproperty
    a1: assert property (p (test_sig));
    c1: cover property (!test_sig ##1 test_sig);
endchecker : my_check1
