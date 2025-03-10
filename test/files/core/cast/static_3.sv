parameter P = 17;
parameter Q = 16;

initial begin
    a = 17'(x - 2);

    b = P'(x - 2);
    c = (Q+1)'(x - 2);

    y = signed'(x);
end
