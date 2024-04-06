// Section 21.4: Constraint
  
virtual class Parent;
   pure constraint C;
endclass;

class Child extends Parent;
  int a, b;
  extern constraint C;         // must be overriden
endclass

constraint Child::C {a > b;}   // example of external constraint


