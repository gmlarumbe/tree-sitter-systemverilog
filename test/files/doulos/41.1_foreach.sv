// Section 41.1: Foreach

string Letters[4] = '{"a", "b", "c", "d"};
foreach(Letters[i])
  $display("Letters[%0d] = %s", i, Letters[i]);

int Mult [0:3][0:7];
foreach (Mult[i,j])
  Mult[i][j] = i * j;    // Initialise

  
