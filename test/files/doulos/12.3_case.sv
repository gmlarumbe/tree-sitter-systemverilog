// Section 12.3: Case

// Pattern-matching case statement
typedef union tagged {
  void Invalid;
  int  Valid;
} VInt;
/*...*/
VInt v;
/*...*/
case (v) matches
  tagged Invalid  : $display ("v is Invalid");
  tagged Valid .n : $display ("v is Valid with value %d", n);
endcase


