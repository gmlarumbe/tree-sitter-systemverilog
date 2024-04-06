module mod;

initial begin
  if (cond) begin
    a = 0;
    if (cond2) begin
      b = 1;
      if (cond3) begin
        c = 2;
      end
    end
  end
end

endmodule
