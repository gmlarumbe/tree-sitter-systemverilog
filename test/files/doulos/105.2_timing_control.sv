// Section 105.2: Timing Control

// Delay a nonblocking assignment to overcome clock skew.
always @(posedge Clock)  
  Count <= #1 Count + 1;


