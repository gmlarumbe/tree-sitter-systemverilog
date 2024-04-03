// Section 29.2: Disable

// Using disable fork to terminate spawned processes.
initial
fork             // Spawns two processes by calling two tasks in parallel
  a_task;
  another_task;
join_any         // Blocks until first process completes
disable fork;    // Terminates the other process

  
