// Section 88.3: Randsequence

// Sequence interleaving
randsequence(Top) 
  Top : rand join S1 S2;
   S1 : A B ;
   S2 : C D ;
   /*...*/
endsequence  // Generates, for example: A B C D.


