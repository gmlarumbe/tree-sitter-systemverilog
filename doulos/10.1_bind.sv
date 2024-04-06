// Section 10.1: Bind

// Binding a module to a module and a module instance
module Test (input bit[7:0] Addr, Data);
  /*...*/
endmodule

module CheckAddr (input bit[7:0] Addr, Max);
    A1: assert property (Addr <= Max)
        else $error("Address is out of range");
endmodule

module RAM (input bit[7:0] Addr, Data /*...*/);
  /*...*/
endmodule

module TestRAM;
  /*...*/
  RAM RAM_inst (Addr, Data, /*...*/);
endmodule

// Binds an instance of the module Test to the testbench
bind TestRAM Test Test_inst(Addr, Data);

// Binds an instance of the module CheckAddr to the RAM instance
bind TestRAM.RAM_inst CheckAddr CA_inst(Addr, Data);

// Alternative syntax for the above
bind RAM: RAM_inst CheckAddr CA_inst(Addr, Data);


