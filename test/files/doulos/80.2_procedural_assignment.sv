// Section 80.2: Procedural Assignment

always @Swap
fork           // Swap the values of a and b
  a = #5 b;
  b = #5 a;
join           // Completes after a delay of 5


