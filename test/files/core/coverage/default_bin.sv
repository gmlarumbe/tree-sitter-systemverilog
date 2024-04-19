module test();

logic [7:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    bins low          = {0,10};
    // All other values are not counted in coverage calculation
    bins lazy         = default;
  }
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  addr <= 0;
  $monitor("ce %b addr 8'h%x",ce,addr);
  repeat (10) begin
    addr = $random();
    ce <= 1;
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
