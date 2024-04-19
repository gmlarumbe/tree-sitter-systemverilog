module test();

logic [2:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    bins adr_0_2times          = (0[*2]);
    bins adr_1_3times          = (1[*3]);
    bins adr_2_4times          = (2[*4]);
  }
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  addr <= 2;
  $monitor("ce %b addr 8'h%x",ce,addr);
  repeat (10) begin
    ce <= 1;
    #10;
    ce <= 0;
    #10;
  end
end

endmodule
