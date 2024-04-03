// Section 22.1: Covergroup

// Covergroup containing options
covergroup CG (string Comment) @(posedge clk);
  option.comment = Comment;   // Comment for each instance of CG
  type_option.strobe = 1;     // Sample at the end of the time slot
  CP1 : coverpoint A {
    option.auto_bin_max = 8;  // Create 8 automatic bins for 
  }                           // coverpoint CP1 for each instance
endgroup


