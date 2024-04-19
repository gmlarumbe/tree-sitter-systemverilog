module test();

logic [2:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    ignore_bins ignore_tran = (0=>2=>1);
    ignore_bins ignore_vals = {0,1,2,3};
    illegal_bins ignore     = {5};
  }
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  $monitor("ce %b addr 8'h%x",ce,addr);
  repeat (10) begin
    ce <= 1;
    addr <= $urandom_range(0,7);
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
