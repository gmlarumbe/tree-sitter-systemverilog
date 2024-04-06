// Section 112.2: Virtual

// Polymorphism example:
BaseClass Bases[2];     // Declare a variable of abstract BaseClass
ExtendClass ExCl = new; // Instance of an ExtendedClass object
Bases[0] = ExCl;        // Legal
shortint x;
/*...*/

initial begin
if (Bases[0].AFunc(x) == 1)     // Invokes the AFunc method
   ;                             // from ExtendClass
  /*...*/
end

