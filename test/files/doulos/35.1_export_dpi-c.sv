// Section 35.1: Export "DPI-C"
  
// SystemVerilog - Exported DPI Function:
module Bus(input In1, output Out1);
  export "DPI-C" function read;
  // This SystemVerilog function can be called from C
  function void read(int data);
    /*...*/
  endfunction
  /*...*/
endmodule


