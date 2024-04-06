// Section 128.1: Expect

module Test;
  initial begin
    /*...*/
    #100ns expect(@(posedge clk) a ##1 b) 
      else $error( "expect failed" );
    /*...*/
  end
endmodule : Test


