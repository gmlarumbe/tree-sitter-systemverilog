// Section 37.1: Extends

class ParentClass;
  int X = 1;
  function int AFunc();
    AFunc = X - 1;
  endfunction
endclass

class ExtendedClass extends ParentClass;
  int X = 2;             // Overridden variable 
  function int AFunc();  // Overridden method
    get = X + 1;
  endfunction
endclass

ExtendedClass EP = new;
ParentClass P = EP;  // Overridden members of ExtendedClass are hidden

Y = P.X;             // Y = 1, not 2
Y = P.AFunc();       // Y = 0, not 3 or 1


