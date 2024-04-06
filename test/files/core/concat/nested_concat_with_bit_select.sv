module x;
    always begin
        a <= {b[1:0], {1'b0,1'b0}};
    end
endmodule
