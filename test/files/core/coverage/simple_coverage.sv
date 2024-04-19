//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With Coverage
//+++++++++++++++++++++++++++++++++++++++++++++++++
module simple_coverage();

logic [7:0]  addr;
logic [7:0]  data;
logic        par;
logic        rw;
logic        en;
//=================================================
// Coverage Group
//=================================================
covergroup memory @ (posedge en);
  address : coverpoint addr {
    bins low    = {0,50};
    bins med    = {51,150};
    bins high   = {151,255};
  }
  parity : coverpoint  par {
    bins even  = {0};
    bins odd   = {1};
  }
  read_write : coverpoint rw {
    bins  read  = {0};
    bins  write = {1};
  }
endgroup
//=================================================
// Instance of covergroup memory
//=================================================
memory mem = new();
//=================================================
// Task to drive values
//=================================================
task drive (input [7:0] a, input [7:0] d, input r);
  #5 en <= 1;
  addr  <= a;
  rw    <= r;
  data  <= d;
  par   <= ^d;
  $display ("@%2tns Address :%d data %x, rw %x, parity %x",
     $time,a,d,r, ^d);
  #5    en <= 0;
  rw    <= 0;
  data  <= 0;
  par   <= 0;
  addr  <= 0;
  rw    <= 0;
endtask
//=================================================
// Testvector generation
//=================================================
initial begin
  en = 0;
  repeat (10) begin
    drive ($random,$random,$random);
  end
  #10 $finish;
end

endmodule
