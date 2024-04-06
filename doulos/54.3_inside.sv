// Section 54.3: Inside

initial begin
int array [$] = '{c, d};
if ( V inside {a, b, array})   // Equiv. to {a, b, c, d}
  /*...*/
    ;
end


