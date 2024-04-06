// Section 102.1: Task Enable

task Counter;
  inout [3:0] Count;
  input Reset;
  /*...*/
endtask

always @(posedge Clock)
  Counter(Count, Reset);

  
