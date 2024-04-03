// Section 2.3: Always

always_ff @(posedge Clk iff Reset == 0 or posedge Reset)
  begin
    // /*...*/
  end

always_ff @(posedge Clock iff nReset or negedge nReset)
  begin
    if (~nReset)                    // Asynchronous reset
      Count <= 0;
    else
      if (~Load)                    // Synchronous load
        Count <= Data;
      else
        Count <= Count + 1;
  end

always_ff @(edge Clk, posedge Reset) // Daul Data Rate (DDR)
  begin                              // clock on both edges
    // /*...*/
  end

always_ff @(Clk, posedge Reset) // Alternative DDR coding style
  begin
    // /*...*/
  end


