// Section 6.2: Assign

// Procedural continuous assignment (Deprecated!)
always @(posedge Clock)
  Count = Count + 1;
always @(Reset)         // Asynchronous Reset
  if (Reset)
    assign Count = 0;   // Prevents counting, until Reset goes low
  else
    deassign Count;     // Resume counting on next posedge Clock


