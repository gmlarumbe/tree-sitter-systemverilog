// Section 54.2: Inside

initial begin
b = a inside {2'b?1};              // Matches 2'b01, 2'b11, 2'x1, 2'bz1
end

