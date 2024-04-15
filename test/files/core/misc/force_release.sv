module foo;
    initial begin
        force f = a && b;
        release f;
    end
endmodule
