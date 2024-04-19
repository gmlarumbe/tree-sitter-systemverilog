//+++++++++++++++++++++++++++++++++++++++++++++++++
// Define the interface with coverage
//+++++++++++++++++++++++++++++++++++++++++++++++++
interface mem_if (input wire clk);
  logic        reset;
  logic        we;
  logic        ce;
  logic  [7:0] datai;
  logic [7:0] datao;
  logic [7:0] addr;
  //=================================================
  // Clocking block for testbench
  //=================================================
  clocking cb @ (posedge clk);
    inout reset, we, ce, datai,addr;
    input  datao;
  endclocking
  //=================================================
  // Modport for testbench 
  //=================================================
  modport  tb (clocking cb, input clk);

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
module coverage_class();

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
class  mem_driver;
  virtual  mem_if.tb cif;

  //=================================================
  // Coverage Group in class
  //=================================================
  covergroup memory @ (negedge cif.cb.ce);
    address : coverpoint cif.cb.addr {
      bins low    = {0,50};
      bins med    = {51,150};
      bins high   = {151,255};
    }
   endgroup

   covergroup datac @ (negedge cif.cb.ce);
     data_in : coverpoint cif.cb.datai {
       bins low    = {0,50};
       bins med    = {51,150};
       bins high   = {151,255};
     }
     data_out : coverpoint cif.cb.datao {
       bins low    = {0,50};
       bins med    = {51,150};
       bins high   = {151,255};
     }
     read_write : coverpoint cif.cb.we {
       bins  read  = {0};
       bins  write = {1};
     }
  endgroup

  function new (virtual mem_if.tb cif);
    this.cif = cif;
    this.datac = new();
    this.memory = new();
  endfunction

  task automatic drive ();
    cif.cb.reset     <= 1;
    cif.cb.ce        <= 1'b0;
    cif.cb.we        <= 1'b0;
    cif.cb.addr      <= 0;
    cif.cb.datai     <= 0;
    @ (cif.cb) cif.cb.reset <= 0;
    for (int i = 0; i < 3; i ++ ) begin
      ##1 cif.cb.ce  <= 1'b1;
      cif.cb.we      <= 1'b1;
      cif.cb.addr    <= i;
      cif.cb.datai   <= $random;
      repeat (3) @ (cif.cb) cif.cb.ce  <= 1'b0;
      $display ("@%0dns Write access address %0x, data %x",
        $time,i,cif.cb.datai);
    end
    for (int i = 0; i < 3; i ++ ) begin
      @ (cif.cb) cif.cb.ce  <= 1'b1;
      cif.cb.we      <= 1'b0;
      cif.cb.addr    <= i;
      repeat (4) @ (cif.cb) cif.cb.ce  <= 1'b0;
      $display ("@%0dns Read access address %0x, data %x",
        $time,i,cif.cb.datao);
    end
  endtask

endclass

mem_driver driver = new(miff);

initial begin
  driver.drive();
  #10 $finish;
end

endmodule
