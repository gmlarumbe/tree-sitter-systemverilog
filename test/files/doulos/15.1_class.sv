// Section 15.1: Class

// Class definition
class Register;
  // Properties
  logic [7:0] data;

  // Methods
  function new (logic[7:0] d = 0); // Constructor
    data = d;
  endfunction

  task load (logic[7:0] d);
    data = d;
  endtask
endclass


