// Section 81.1: Process

initial
  begin
    // Declare a process variable
    process p;
    // Spawn a process
    fork
      begin
        // Obtain process's handle
        p = process::self();
        /*...*/
      end
    join_none  // Nonblocking
    // If the process hasn't completed after 100ns, forcibly terminate it
    #100ns if (p != process::FINISHED) p.kill();
  end


