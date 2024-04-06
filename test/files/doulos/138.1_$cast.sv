// Section 138.1: $cast

typedef enum {A, B, C, D} ABCD;
ABCD Letter;
$cast( Letter, 1+1);  // Equivalent to Letter = ABCD'(1+1);

// Check if the assignment is legal
if (!$cast( Letter, 1 + 4) ) // 5: invalid cast
  $display("Casting Error");


