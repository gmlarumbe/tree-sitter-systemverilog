// Section 88.2: Randsequence

initial begin
randsequence(Top)
  Top : One Two Three Four;
  One : S11 | S12;
  // Sequence aborted after S21 if i < 2
  Two : S21 {if (i < 2) break;} S22;
  Three : case (j)
          0    : S31;           // If j=0, S31 is generated
          1, 2 : S32;           // If j=1 or 2, S32 is generated
          default : S33;        // Otherwise, S33 is generated
        endcase ;
  // Repeat S4 a random no. of times in the range [1:3], depending on the
  // value returned by $urandom_range()
  Four : repeat($urandom_range(1, 3)) S4;
  S11 : {$display("S11");} ;
  S12 : {$display("S12");} ;
  S21 : {i--; $display("S21");} ;
  S22 : {i++; $display("S22");} ;
  /*...*/
endsequence
  end


