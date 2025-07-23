module foo;
  initial begin
    if (1'b1) begin
        // ...
    end
`ifdef FOO
    else begin
        // ...
    end
`endif
  end
endmodule
