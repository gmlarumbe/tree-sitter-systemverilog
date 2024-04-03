// Section 149.1: Stochastic Modelling

module Queues;

  parameter Queue = 1;  // Q_id
  parameter Fifo = 1, Lifo = 2;
  parameter QueueMaxLen = 8;
  integer Status, Code, Job, Value, Info;
  reg IsFull;

  task Error;           // Write error message and quit
    /*...*/
  endtask

  initial
  begin
// Create the queue
    $q_initialize(Queue, Lifo, QueueMaxLen, Status);
    if ( Status )
      Error("Couldn't initialize the queue");

// Add jobs
    for (Job = 1; Job <= QueueMaxLen; Job = Job + 1)
    begin
      #10 Info = Job + 100;
      $q_add(Queue, Job, Info, Status);
      if ( Status )
        Error("Couldn't add to the queue");
      $display("Added Job %0d, Info = %0d", Job, Info);
      $write("Statistics: ");
      for ( Code = 1; Code <= 6; Code = Code + 1 )
      begin
        $q_exam(Queue, Code, Value, Status);
        if ( Status )
          Error("Couldn't examine the queue");
        $write("%8d", Value);
      end
      $display("");
    end

// Queue should now be full
    IsFull = $q_full(Queue, Status);
    if ( Status )
      Error("Couldn't see if queue is full");
    if ( !IsFull )
      Error("Queue is NOT full");

// Remove jobs
    repeat ( 10 ) begin
      #5 $q_remove(Queue, Job, Info, Status);
      if ( Status )
        Error("Couldn't remove from the queue");
      $display("Removed Job %0d, Info = %0d", Job,Info);
      $write("Statistics: ");
      for ( Code = 1; Code <= 6; Code = Code + 1 )
      begin
        $q_exam(Queue, Code, Value, Status);
        if ( Status )
          Error("Couldn't examine the queue");
        $write("%8d", Value);
      end
      $display("");
    end
  end
endmodule


