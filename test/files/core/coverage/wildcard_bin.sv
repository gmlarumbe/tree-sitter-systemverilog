module test();

logic [2:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    // Normal transition bibs
    wildcard bins adr0  = {3'b11?};
    // We can use wildcard in transition bins also
    wildcard bins adr1  = (3'b1x0 => 3'bx00);
    wildcard bins adr2  = (3'b1?0 => 3'b?00);
  }
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  $monitor("ce %b addr 8'h%x",ce,addr);
  repeat (10) begin
    ce <= 1;
    addr <= $urandom_range(0,2);
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
