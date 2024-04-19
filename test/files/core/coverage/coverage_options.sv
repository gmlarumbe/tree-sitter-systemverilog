module test();

logic [2:0] addr;
wire [2:0] addr2;
reg ce;

assign addr2 = addr + 1;

covergroup address_cov () @ (posedge ce);
  option.name         = "address_cov";
  option.comment      = "This is cool";
  option.per_instance = 1;
  option.goal         = 100;
  option.weight       = 50;
  ADDRESS : coverpoint addr {
    option.auto_bin_max = 100;
  }
  ADDRESS2 : coverpoint addr2 {
    option.auto_bin_max = 10;
  }
endgroup

address_cov my_cov = new();

initial begin
  my_cov.ADDRESS.option.at_least = 1;
  my_cov.ADDRESS2.option.at_least = 2;
  ce   <= 0;
  $monitor("ce %b addr 8'h%x addr2 8'h%x",ce,addr,addr2);
  repeat (10) begin
    ce <= 1;
    addr <= $urandom_range(0,7);
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
