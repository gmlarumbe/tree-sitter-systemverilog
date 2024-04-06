// Section 21.1: Constraint

class foo;
constraint c1 {a == 4;}
constraint c2 {b > 3; c > 10;}
constraint valid_parity {parity_ok dist {0:=1, 1:=9};}
constraint c3 {size == BIG -> len > 20;}
constraint c4 {i inside {1,[2:3]};}  // Equiv. to i==1 || i==2 || i==3
constraint c5 {solve b,c before a;}
constraint c6 {unique{a,b,c};}  // (a != b) && (b != c) && (c != a)
endclass

