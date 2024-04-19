module expect_assertion;

logic clk = 0;
always #1 clk ++;

logic a, b,c;

default clocking myclk @ (posedge clk);

endclocking

initial begin 
  a <= 0;
  b <= 0;
  c <= 0;
  ##1;
  a <= 1;
  ##1;
  a <= 0;
  b <= 1;
  ##1;
  b <= 0;
  c <= 0;
  ##1;
  c <= 0;
  ##20000 $finish;
end

initial begin
  ##1;
  // Wait for the sequence if pass, terminate sim
  expect ( @ (posedge clk) a ##1 b ##1 c ##1 !c)
     $finish;
   else
     $error ("Something is wrong");
end
  
endmodule
