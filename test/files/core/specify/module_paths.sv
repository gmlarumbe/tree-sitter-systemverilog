specify

    (A => Q) = 10;
    (B => Q) = (12);
    (C, D *> Q) = 18;

    (posedge clock => (out +: in)) = (10, 8);

    (negedge clock[0] => (out -: in)) = (10, 8);

    (clock => (out : in)) = (10, 8);

endspecify
