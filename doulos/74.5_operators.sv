// Section 74.5: Operators

// Class scope resolution operator
class BaseClass;
  int x;
  static task ATask(int i, int j);
   /*...*/ 
  endtask
endclass
/*...*/
BaseClass B = new;
int x = 1;
B.ATask(BaseClass::x, x); // BaseClass::x and x are different


