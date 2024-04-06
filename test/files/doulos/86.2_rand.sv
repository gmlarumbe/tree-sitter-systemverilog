// Section 86.2: Rand

// Seeding
class B;
  rand bit a;
  function new (int seed);
    this.srandom(seed);
    /*...*/
  endfunction
  /*...*/
endclass 

B b = new(8);            // Create b with seed = 8
b.srandom(10);           // Re-seed b with seed 10


