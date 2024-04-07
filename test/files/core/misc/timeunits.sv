// Declaration in Unit Scope
timeunit 100ps;
timeprecision 10fs;

// Declaration in modules
module A ();
  timeunit 100ps;
  timeprecision 10fs;
  // ...
endmodule

module B ();
  timeunit 100ps / 10fs; // timeunit with optional second argument
  // ...
endmodule

module C ();
  timeunit 100ps; timeprecision 10fs; // Colon-separated declaration (1)
  // ...
endmodule

module D ();
  timeprecision 10fs; timeunit 100ps;  // Colon-separated declaration (2)
  // ...
endmodule
