extern interface m (a,b,c,d);

extern interface a #(parameter size = 8, parameter type TP = logic [7:0])
    (input [size:0] a, output TP b);

interface m (.*);
    input a,b,c;
    output d;
endinterface
