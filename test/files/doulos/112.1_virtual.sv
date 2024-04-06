// Section 112.1: Virtual

virtual class BaseClass;  // Class that cannot be instantiated
  pure virtual function int AFunc(int x);
endclass

class ExtendClass extends BaseClass;   // Subclass
  function int AFunc(int x); // Prototype identical to the Base Class
    AFunc = x - 1;
  endfunction
endclass


