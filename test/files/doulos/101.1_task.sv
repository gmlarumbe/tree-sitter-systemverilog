// Section 101.1: Task

// Simple RTL task, which can be synthesized.
task Counter;
  inout [3:0] Count;
  input Reset;
  if (Reset)         // Synchronous Reset
    Count = 0;       // Must use blocking, or value won't be seen
  else
    Count = Count + 1;
endtask


