// Section 16.3: Clocking

// Clocking Block Drives
CB1.Data[2:0] <= 3'h3;    // Drive 3-bit slice of Q in current cycle
##1 CB1.Data <= 4'hz;     // Wait 1 Clk cycle and then drive Q
##3 CB1.Data[3] <= 1'b0;  // Wait 3 Clk cycles, then drive bit 3 of Q
CB1.Data <= ##2 Int_Data; // Remember Int_Data, then drive Data after 2 clocks


