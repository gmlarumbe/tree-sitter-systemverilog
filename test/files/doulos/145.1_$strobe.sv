// Section 145.1: $strobe

initial
begin
  a = 0;
  $display(a);                // Displays 0
  $strobe(a);                 // Displays 1 /*...*/
  a = 1;                      // /*...*/ because of this statement

end

