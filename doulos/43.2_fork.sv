// Section 43.2: Fork

initial
fork
  first_process;
  second_process;
  wait(interrupt);
join_any             // Completes when either process completes, or
                     // an interrupt occurs

					 
