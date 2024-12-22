module test(
	input port_a,
`ifdef FOO
	input port_b,
`endif

	output port_c
);
	
`ifdef FOO
	assign port_c = port_b;
`else
	assign port_c = port_a;
`endif

endmodule: test