// Section 4.2: Array Manipulation Methods

// Find all items in Ar1 that are greater than corresponding item in Ar2
int Ar1[3:0][3:0], Ar2[3:0][3:0];
int r[$];
r = Ar1.find(x) with (x > Ar2[x.index(1)][x.index(2)]);      


