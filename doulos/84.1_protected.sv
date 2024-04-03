// Section 84.1: Protected

class BaseClass;
  extern virtual protected function int AFunc(bit X); // Prototype
  extern protected virtual function int BFunc(int Y);
endclass

class ExtendedClass extends BaseClass;
  protected function int AFunc(bit X);
    /*...*/ // Function body
  endfunction
endclass


