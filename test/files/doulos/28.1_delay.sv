// Section 28.1: Delay

module foo;
    and #(5) a1 (out, in1, in2);         // Only one delay
    bufif0 #(1,2,3) b1 (out, in, ctrl);  // Rise, fall and turn-off
    // delays
    not #5ns n1 (ndata, data);
    bufif1 #(1:2:3, 4:6:8, 5:10:12) b2 (io2, io1, dir);
endmodule

