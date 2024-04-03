// Section 105.1: Timing Control

initial begin
#10;
#10ns;
#(Period/2);
#(1.2:3.5:7.1);
@Trigger;
@(a or b or c);
@(a, b, c);
@(*);
@(posedge clock or negedge reset);
end

