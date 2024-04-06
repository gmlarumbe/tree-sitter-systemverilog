// Section 16.2: Clocking

// Synchronization statements - the events are sampled according to the clock domain timing:
@(CB1.Q);            // Wait for the next change of Q from CB1 domain
@(negedge CB1.Load); // Wait for negative edge of signal CB1.Load
@(posedge CB1.Load or negedge CB1.UpDn);
@(CB1.Q[1]);         // Wait for the next change of bit 1 of CB1.Q
@(CB1.Q[2:0]);       // Wait for the next change of the specified slice


