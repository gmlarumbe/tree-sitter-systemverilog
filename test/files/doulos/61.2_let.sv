// Section 61.2: Let

module n;
  logic clock, j;
  let Rose(e, j) = $rose(j, @(e));
  /*...*/
  always /*...*/
    if ( Rose( posedge clock, j) ) // event argument
      /*...*/ ;
  /*...*/
endmodule


