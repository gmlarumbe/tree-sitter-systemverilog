// Section 88.1: Randsequence

// The following generates either ABC or ABD. The latter is twice as likely.
initial begin
randsequence()
   S1 : A B S2;                         // Sequence starts here
   S2 : C | D := 2;
   A  : {$display("A");};
   B  : {$display("B");};
   C  : {$display("C");};
   D  : {$display("D");};
endsequence
end

