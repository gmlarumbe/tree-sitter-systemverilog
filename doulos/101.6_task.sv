// Section 101.6: Task

// Tasks in a testbench
module TestRAM;

  parameter AddrWidth = 5;
  parameter DataWidth = 8;
  parameter MaxAddr = 1 << AddrBits;

  reg [DataWidth-1:0] Addr;
  reg [AddrWidth-1:0] Data;
  wire [DataWidth-1:0] DataBus = Data;
  reg Ce, Read, Write;

  Ram32x8 Uut (.Ce(Ce), .Rd(Read), .Wr(Write),
               .Data(DataBus), .Addr(Addr));

  initial
  begin : stimulus
    integer NErrors;
    integer i;
    // Initialize the error count
    NErrors = 0;
    // Write the address value to each address
    for ( i=0; i<=MaxAddr; i=i+1 )
      WriteRam(i, i);
    // Read and compare
    for ( i=0; i<=MaxAddr; i=i+1 )
    begin
      ReadRam(i, Data);
      if ( Data !== i )
        RamError(i,i,Data);
    end
    // Summarise the number of errors
    $display("Completed with %0d errors", NErrors);
  end

  task WriteRam;
    input [AddrWidth-1:0] Address;
    input [DataWidth-1:0] RamData;

    Ce = 0;
    Addr = Address;
    Data = RamData;
    #10 Write = 1;
    #10 Write = 0;
    Ce = 1;
  endtask

  task ReadRam;
    input  [AddrWidth-1:0] Address;
    output [DataWidth-1:0] RamData;

    Ce = 0;
    Addr = Address;
    Data = RamData;
    Read = 1;
    #10 RamData = DataBus;
    Read = 0;
    Ce = 1;
  endtask

  task RamError;
    input [AddrWidth-1:0] Address;
    input [DataWidth-1:0] Expected;
    input [DataWidth-1:0] Actual;
    if ( Expected !== Actual )
    begin
      $display("Error reading address %h", Address);
      $display("  Actual %b, Expected %b", Actual, Expected);
      NErrors = NErrors + 1;
    end
  endtask
endmodule


