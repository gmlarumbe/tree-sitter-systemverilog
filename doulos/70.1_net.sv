// Section 70.1: Net

wire Clock;
wire [7:0] Address;
wire enum {red, green, blue} light;
tri1 [31:0] Data, Bus;
trireg (large) C1, C2;
wire f = a && b,
     g = a || b;           // Continuous assignments

	 
