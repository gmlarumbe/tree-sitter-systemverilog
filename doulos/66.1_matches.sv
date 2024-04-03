// Section 66.1: Matches

typedef union tagged packed {
  void Invalid;
  int Valid;
} VInt;

VInt v;
int j;

//Pattern-matching case statement:
case (v) matches
  tagged Invalid  : $display("v's value is invalid");
  tagged Valid .n : $display("v is valid: value is %d", n);
endcase

//Pattern-matching if statement:
if (v matches tagged Invalid)
  $display("v's value is invalid");
else if (v matches tagged Valid .n &&& n < 0)
  $display("v is valid, and negative");

// Pattern-matching conditional operator:
j = v matches tagged Valid .n ? n : 'x;


