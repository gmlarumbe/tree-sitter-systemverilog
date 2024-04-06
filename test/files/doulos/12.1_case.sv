// Section 12.1: Case

case (Address)
  0 : A <= 1;        // Select a single Address value
  1 : begin          // Execute more than one statement
        A <= 1;
        B <= 1;
      end
  2, 3, 4 : C <= 1;  // Pick out several Address values
  default :          // Mop up the rest
    $display("Illegal Address value %h in %m at %t",
             Address, $realtime);
endcase


