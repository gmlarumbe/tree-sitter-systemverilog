// Section 43.3: Fork

initial
  for(int j = 0; j <= 3; j++)
    fork
      automatic int k = j;
      process1: begin /*...*/ end
      process2: begin /*...*/ end
      /*...*/
    join_none

	
