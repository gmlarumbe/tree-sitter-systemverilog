module test();

logic [7:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
     // Set this option to limit number of auto bins created
     option.auto_bin_max = 10;
    // See no bins are declared here, Not a good idea
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
