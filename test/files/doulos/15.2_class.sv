// Section 15.2: Class

// Using the Register class
Register accum;  // accum stores a handle to an object of class Register
accum = new;     // Create a new Register object; its handle is in accum
Register accum1 = new;         // Alternative
Register accum2 = new(8'hff);  // Initialize
Register accum3[10];
  foreach (accum3[i]) accum3[i] = new; // Array of 10 Registers

accum.data = 8'h1f;         // Store value in data member
accum.load(8'h1f);          // A better way of doing it


