// Section 44.1: Forkjoin

interface bus #(parameter N = 0) (input logic clock);
  extern forkjoin
    task slave_write(bit[7:0] Addr, bit[7:0] Data);
  extern forkjoin task slave_read(bit[7:0] Addr);
  modport slave_if (export task slave_write(bit[7:0] Addr, 
                      bit[7:0] Data),
                    export task slave_read(bit[7:0] Addr));
  /*...*/
endinterface

module mem (bus busport);
  task busport.slave_write(bit[7:0] Addr, bit[7:0] Data);
   /*...*/
  endtask
  /*...*/
endmodule


