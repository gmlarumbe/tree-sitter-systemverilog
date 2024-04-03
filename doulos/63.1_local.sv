// Section 63.1: Local

class AClass;
  local int i;
  function int AFunc (AClass A);
    AFunc = this.i + A.i; // A.i is a local property referenced outside 
                          // its instance, but within the same class
  endfunction
endclass


