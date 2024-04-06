// Section 4.1: Array Manipulation Methods

byte b[] = '{1, 3, 2};
byte s, r[$];
r = b.find(x) with (x > 2);          // r = {3}
r = b.find with (item == item.index);// find all items equal to their 
                                     // index, i.e. {2}
r = b.min;                           // r = 1
b.reverse;                           // b = '{2, 3, 1}
b.sort;                              // b = '{1, 2, 3}
s = b.sum with (item + 4);           // s = 18 (i.e. 5 + 7 + 6)
s = b.xor;                           // s =  0 (i.e. 1 ^ 3 ^ 2)

  
