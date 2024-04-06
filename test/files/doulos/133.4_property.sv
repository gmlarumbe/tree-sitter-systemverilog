// Section 133.4: Property

// Recursive properties
property RecP1(p);
  p and (1'b1 |=> RecP1(p));
endproperty

property RecP2;   
  s1 |-> (prop2 and (1'b1 |=> RecP3));
endproperty

property RecP3;          // RecP2 and RecP3 are mutually recursive
  s2 |-> (prop3 and (1'b1 |=> RecP2));
endproperty


