module test();

logic [2:0] addr;
wire [2:0] addr2;

assign addr2 = addr + 1;

covergroup address_cov;
  ADDRESS : coverpoint addr {
    option.auto_bin_max = 10;
  }
  ADDRESS2 : coverpoint addr2 {
    option.auto_bin_max = 10;
  }
endgroup

address_cov my_cov = new;

initial begin
  my_cov.ADDRESS.option.at_least = 1;
  my_cov.ADDRESS2.option.at_least = 2;
  // start the coverage collection
  my_cov.start();
  // Set the coverage group name
  my_cov.set_inst_name("ASIC-WORLD");
  $monitor("addr 8'h%x addr2 8'h%x",addr,addr2);
  repeat (10) begin
    addr = $urandom_range(0,7);
    // Sample the covergroup
    my_cov.sample();
    #10;
  end
  // Stop the coverage collection
  my_cov.stop();
  // Display the coverage
  $display("Instance coverage is %e",my_cov.get_coverage());
end

endmodule
