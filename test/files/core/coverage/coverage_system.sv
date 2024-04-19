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
  // Set the database name
  $set_coverage_db_name("asic_world");
  $monitor("addr 8'h%x addr2 8'h%x",addr,addr2);
  repeat (10) begin
    addr = $urandom_range(0,7);
    my_cov.sample();
    #10;
  end
  // Get the final coverage
  $display("Total coverage %e",$get_coverage());
end

endmodule
