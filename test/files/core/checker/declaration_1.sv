// Simple checker containing deferred assertions
checker my_check2 (logic a, b);
    a1: assert #0 ($onehot0({a, b}));
    c1: cover #0 (a == 0 && b == 0);
    c2: cover #0 (a == 1);
    c3: cover #0 (b == 1);
endchecker : my_check2
