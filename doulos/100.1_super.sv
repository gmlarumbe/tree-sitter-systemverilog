// Section 100.1: Super

class ParentClass;
  int X = 1;
  function int AFunc();
    AFunc = 2*X;
  endfunction
endclass

class DerivedClass extends ParentClass;
  int X = 2;                  // Overridden variable 
  function int AFunc();  
    AFunc = super.AFunc() + 2*X*super.X;
  endfunction
endclass


