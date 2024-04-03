// Section 69.3: Name

// Hierarchical names, and an upwards name reference.
module Separate;
  parameter P = 5;     // Separate.P or $root.Separate.P
endmodule

module Top;
  logic R;             // Top.R or $root.Top.R
  Bottom U1();
endmodule

module Bottom;
  logic R;             // Top.U1.R or $root.Top.U1.R 

  task T;              // Top.U1.T or $root.Top.U1.T 
    logic R;           // Top.U1.T.R or $root.Top.U1.T.R
    /*...*/
  endtask

  initial
  begin : InitialBlock
    logic R;             // $root.Top.U1.InitialBlock.R
    $display(Bottom.R);  // Upwards name reference to Top.U1.R
    $display(U1.R);      // Upwards name reference to Top.U1.R
    /*...*/
  end
endmodule


