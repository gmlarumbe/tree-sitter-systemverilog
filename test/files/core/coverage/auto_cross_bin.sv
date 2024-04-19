module test();

logic [2:0] addr;
logic [1:0] cmd;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    bins addr0 = {0};
    bins addr1 = {1};
    bins addr2 = {2};
    bins addr3 = {3};
  }
  CMD : coverpoint cmd {
    bins READ = {0};
    bins WRITE = {1};
    bins IDLE  = {2};
  }
  CRS_ADDR_CMD : cross ADDRESS, CMD;
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  $monitor("ce %b addr 8'h%x cmd %x",ce,addr,cmd);
  repeat (10) begin
    ce <= 1;
    addr <= $urandom_range(0,5);
    cmd  <= $urandom_range(0,2);
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
