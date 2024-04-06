// Section 15.5: Class

// Out of class method definitions
task ShiftRegister::shiftleft();
  data = data << 1;
endtask

task ShiftRegister::shiftright();
  data = data >> 1;
endtask

ShiftRegister SR = new;
SR.load(8'h55);                        // Inherited method
SR.shiftleft;                          // data now has 8'aa


