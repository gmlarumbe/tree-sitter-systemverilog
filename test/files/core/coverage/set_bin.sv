module test();

logic [2:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    // simple transition bin
    bins adr_low[]          = (0,1=>2,3);
    bins adr_med[]          = (1,2=>3,4);
    bins adr_high[]         = (3,4=>5,6);
  }
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  addr <= 0;
  $monitor("ce %b addr 8'h%x",ce,addr);
  repeat (10) begin
    ce <= 1;
    addr <= $random;
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
