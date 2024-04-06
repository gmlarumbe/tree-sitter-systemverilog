// Section 22.3: Covergroup

// Covergroups in classes
class Class1;
  bit AnEv;
endclass

class Class2;
  Class1 C1;                 // Object of Class1
  int Var;
  bit X;
  local logic Y,Z;
  
  covergroup CG1 @(C1.AnEv);   // Sampled on data member of C1
    coverpoint Var;
  endgroup 
  
  covergroup CG2 (int Arg) @X; // Second covergroup in the same
                               // class, now having arguments 
    option.at_least = Arg;    // Sets a coverage option of CG2
    coverpoint Y; 
  endgroup
  
  function new(int p);
    CG2 = new(p);
    C1 = new;  // C1 must be instantiated before CG1, because CG1  
               // uses it
    CG1 = new; 
  endfunction
endclass

initial begin
  Class2 Obj = new(7);
end


