// Section 114.4: Wait

// Example using wait fork
initial
  begin         // Parent process
    fork
      /*...*/
    join_none
    wait fork;  // Blocks (waits) until all process spawned by this
                // process have finished
  end


