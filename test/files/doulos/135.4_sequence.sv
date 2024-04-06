// Section 135.4: Sequence

// Dynamic creation of a variable and its assignment
sequence SubSeq(lv); // Declare lv as formal argument
  // a ##1 !a, lv = b ##1 !c*[0:$] ##1 c && (d == lv); // Original one
  a ##1 (!a, lv = b) ##1 !c[0:$] ##1 c && (d == lv);  // Modified to fix syntax errors
endsequence

sequence Seq;
  int Var;
  c ##1 SubSeq(Var) ##1 (a == Var); // Var is bound to lv
endsequence


