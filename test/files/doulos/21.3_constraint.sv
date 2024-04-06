// Section 21.3: Constraint

class foo;
constraint c7 {soft a[0]==0; soft b[0]==1;} // lower priority

task t;
  a.randomize() with {soft a[0]==1; b[0]==0;}; // higher priority
endtask
endclass

