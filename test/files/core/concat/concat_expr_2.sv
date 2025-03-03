module x;
    always begin
        lhs <= {(a[1:0] - b[1:0]), 1'b0};
    end
endmodule
