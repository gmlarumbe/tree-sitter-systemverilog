module test();

logic [7:0] addr;
reg ce;

covergroup address_cov () @ (posedge ce);
  ADDRESS : coverpoint addr {
    // simple transition bin
    bins adr_0_to_1          = (0=>1);
    bins adr_1_to_0          = (1=>0);
    bins adr_1_to_2          = (1=>2);
    bins adr_2_to_1          = (1=>0);
    bins allother            = default sequence;
  }
endgroup

address_cov my_cov = new();

initial begin
  ce   <= 0;
  addr <= 0;
  $monitor("ce %b addr 8'h%x",ce,addr);
  repeat (10) begin
    ce <= 1;
    #10;
    ce <= 0;
    addr ++;
    #10;
  end
end

endmodule
