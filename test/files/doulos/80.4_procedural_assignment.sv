// Section 80.4: Procedural Assignment

// Delay a nonblocking assignment to overcome clock skew.
always @(posedge Clock)
  Count <= #1 Count + 1;


