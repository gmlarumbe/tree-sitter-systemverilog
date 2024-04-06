module x;
    always begin
        a <= {WIDTH*DEPTH{1'b0}};
    end
endmodule
