// Section 58.1: Interface Class

interface class IF1;
  pure virtual function void f();
endclass

interface class IF2;
  pure virtual function void g();
endclass

interface class IF3 extends IF2;
  pure virtual function int h();
endclass

class C;
  function bit i();
  /*...*/
  endfunction
endclass

class D extends C implements IF1, IF3;
  virtual function void f();
  /*...*/
  endfunction

  virtual function void g();
  /*...*/
  endfunction

  virtual function int h();
  /*...*/
  endfunction

  function bit i();
  /*...*/
  endfunction
endclass


