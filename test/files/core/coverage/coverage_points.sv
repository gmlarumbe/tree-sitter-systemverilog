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
  covergroup memory @ (posedge ce);
    address : coverpoint addr {
      bins low    = {0,50};
      bins med    = {51,150};
      bins high   = {151,255};
    }
    data_in : coverpoint datai {
      bins low    = {0,50};
      bins med    = {51,150};
      bins high   = {151,255};
    }
    data_out : coverpoint datao {
      bins low    = {0,50};
      bins med    = {51,150};
      bins high   = {151,255};
    }
    read_write : coverpoint we {
      bins  read  = {0};
      bins  write = {1};
    }
  endgroup
  //=================================================
  // Instance of covergroup
  //=================================================
  memory mem = new();

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
