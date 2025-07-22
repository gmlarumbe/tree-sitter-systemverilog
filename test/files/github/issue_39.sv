module foo;
    initial begin
        case (a)
            2'b00: bar();
            2'b01: baz();
`ifdef FOO
            2'b10: quz();
`endif
        endcase
    end
endmodule
