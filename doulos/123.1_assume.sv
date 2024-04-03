// Section 123.1: Assume

a1: assume property (@(posedge clk) ack |=> !ack);
a2: assume property (@(posedge clk) req dist {0:=1, 1:=9});


