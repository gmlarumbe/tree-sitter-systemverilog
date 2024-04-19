//+++++++++++++++++++++++++++++++++++++++++++++++++
// Define the interface with coverage
//+++++++++++++++++++++++++++++++++++++++++++++++++
interface mem_if (input wire clk);
  logic       reset;
  logic       we;
  logic       ce;
  logic [7:0] datai;
  logic [7:0] datao;
  logic [7:0] addr;
  //=================================================
  // Clocking block for testbench
  //=================================================
  clocking cb @ (posedge clk);
    output reset, we, ce, datai,addr;
    input  datao;
  endclocking
  //=================================================
  // Coverage Group in interface
  //=================================================
  covergroup address_cov (ref logic [7:0] address,
       input int low, int high) @ (posedge ce);
    ADDRESS : coverpoint address {
      bins low    = {0,low};
      bins med    = {low,high};
    }
  endgroup
  //=================================================
  // Instance of covergroup
  //=================================================
  address_cov acov_low  = new(addr,0,10);
  address_cov acov_med  = new(addr,11,20);
  address_cov acov_high = new(addr,21,30);

endinterface
//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With interface
//+++++++++++++++++++++++++++++++++++++++++++++++++
module simple_if (mem_if mif);
// Memory array
logic [7:0] mem [0:255];

//=================================================
// Read logic
//=================================================
always @ (posedge mif.clk)
 if (mif.reset) mif.datao <= 0;
 else if (mif.ce && !mif.we) mif.datao <= mem[mif.addr];

//=================================================
// Write Logic
//=================================================
always @ (posedge mif.clk)
 if (mif.ce && mif.we) mem[mif.addr] <= mif.datai;

endmodule

//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Testbench
//+++++++++++++++++++++++++++++++++++++++++++++++++
module coverage_covergroup();

logic clk = 0;
always #10 clk++;
//=================================================
// Instianciate Interface and DUT 
//=================================================
mem_if miff(clk);
simple_if U_dut(miff);
//=================================================
// Default clocking  
//=================================================
default clocking dclk @ (posedge clk);

endclocking
//=================================================
// Test Vector generation
//=================================================
initial begin
  miff.reset     <= 1;
  miff.ce        <= 1'b0;
  miff.we        <= 1'b0;
  miff.addr      <= 0;
  miff.datai     <= 0;
  ##1 miff.reset <= 0;
  for (int i = 0; i < 3; i ++ ) begin
    ##1 miff.ce  <= 1'b1;
    miff.we      <= 1'b1;
    miff.addr    <= i;
    miff.datai   <= $random;
    ##3 miff.ce  <= 1'b0;
    $display ("@%0dns Write access address %x, data %x",
      $time,miff.addr,miff.datai);
  end
  for (int i = 0; i < 3; i ++ ) begin
    ##1 miff.ce  <= 1'b1;
    miff.we      <= 1'b0;
    miff.addr    <= i;
    ##3 miff.ce  <= 1'b0;
    $display ("@%0dns Read access address %x, data %x",
      $time,miff.addr,miff.datao);
  end
  #10 $finish;
end

endmodule
