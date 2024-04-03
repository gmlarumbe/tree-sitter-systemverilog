// Section 37.2: Extern

// Extern in Interfaces
interface circbuff_if;
  extern function void read (int data);
  extern function void write (int data);
endinterface: circbuff_if

module circbuff #(parameter int size)( circbuff_if Interf);
  function void Interf.write(int data);
    /*...*/
  endfunction
endmodule


