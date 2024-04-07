extern program m (a,b,c,d);

extern program a #(parameter size = 8, parameter type TP = logic [7:0])
    (input [size:0] a, output TP b);

program m (.*);
    input a,b,c;
    output d;
endprogram
