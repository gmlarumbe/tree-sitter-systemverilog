// Section 113.1: Virtual Interface

interface Bus;
  logic passenger;
endinterface

class BusTransactor;
  virtual interface Bus bus;

  function new (virtual Bus b);
    bus = b;
  endfunction

  task do_something (i);
    bus.passenger = i;
  endtask
endclass

module Slave (Bus bus); /*...*/ endmodule

module Test;
  Bus bus1(), bus2();
  Slave slave_inst1 (bus1);
  Slave slave_inst2 (bus2);
  BusTransactor t1, t2;

  initial
    begin
      t1 = new(bus1);
      t2 = new(bus2);
      t1.do_something(0);       // bus1.passenger = 0
      t2.do_something(1);       // bus2.passenger = 1
    end
endmodule


