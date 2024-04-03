// Section 143.1: $readmemb/h, $writememb/h

module Test;
  reg a,b,c,d;
  parameter NumPatterns = 100;
  integer Pattern;

  reg [3:0] Stimulus[1:NumPatterns];

  MyDesign UUT (a,b,c,d,f);

  initial
  begin
    $readmemb("Stimulus.txt", Stimulus);
    Pattern = 0;
    repeat (NumPatterns)
    begin
      Pattern = Pattern + 1;
      {a,b,c,d} = Stimulus[Pattern];
      #110;
    end
  end

  initial
    $monitor("%t a=%b b=%b c=%b d=%b : f=%b",
             $realtime, a, b, c, d, f);

endmodule
 

