// Section 101.2: Task

// An automatic task
task automatic PipelinedMult(
  input [7:0] A, B,
  input integer Depth,
  output [15:0] Y
);                   // ANSI-style arguments
logic [15:0] temp;   // a distinct temp for each running instance of
                     // PipelinedMult due to automatic keyword
  begin
    temp = A * B;
    repeat (Depth)
      @(posedge clk)
    Y = temp;
  end
endtask


