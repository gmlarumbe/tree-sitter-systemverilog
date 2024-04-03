// Section 50.1: Implements

interface class IF1;
  pure virtual function void f();
endclass

class C implements IF1;
  virtual function void f();
  endfunction
endclass;

class D extends C;
endclass


