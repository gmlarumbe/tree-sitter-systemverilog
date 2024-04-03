// Section 37.1: Extern

// Extern in classes
class AClass;
  // Extern declaration
  extern protected virtual function int AFunc(int x);
endclass

function int AClass::AFunc(int x);
// Removed protected, virtual, added AClass::
// The rest of the declaration matches exactly the prototype
  /*...*/  // Method body
endfunction

class PClass #(type T = int);
  extern function T PFunc(int x);
endclass

function PClass::T PClass::PFunc(int x);  // parameterized
  /*...*/
endfunction


