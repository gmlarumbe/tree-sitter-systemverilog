// Section 52.1: Import "DPI-C"

// SystemVerilog - Imported DPI Function:
module Bus();
  import "DPI-C" function void slave_write(input int data);
  function void write(int data);
    // Call C function
    slave_write(data); 
  endfunction
  /*...*/
endmodule


