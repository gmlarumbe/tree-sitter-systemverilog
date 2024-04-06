// Section 151.1: Value Change Dump

module Test;
  /*...*/
  initial
  begin
    $dumpfile("results.vcd");
    $dumpvars(1, Test);
  end

// Perform periodic checkpointing of the design.
  initial
    forever
      #10000 $dumpall;
endmodule

