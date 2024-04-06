module abc ();

always_comb
case ( foo )
  8'h00, 8'h05: bar <= 1'b0;
  default       bar <= 1;
endcase

endmodule

