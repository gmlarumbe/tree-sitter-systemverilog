module x;
    always begin
        lhs <= {(a[N-1:0] - b[N-1:0]), 1'b0};
    end
endmodule
