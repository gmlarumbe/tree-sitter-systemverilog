module mod;

    initial begin
        if (cond) begin
            a = 0;
            if (cond2) begin
                b = 1;
                if (cond3) begin
                    c = 2;
                end else begin
                    c = 0;
                end
            end
            else begin
                b = 0;
            end
        end
        else begin
            a = 1;
        end
    end

endmodule
