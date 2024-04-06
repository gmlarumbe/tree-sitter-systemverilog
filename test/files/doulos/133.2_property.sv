// Section 133.2: Property

// Clock inferred from procedural block
always @(posedge clk) assert property ((a ##2 b)); 

// Clock from clocking block
clocking cb1 @(posedge clk);
  property P1; (a ##2 b); endproperty
endclocking
assert property (cb1.P1);


