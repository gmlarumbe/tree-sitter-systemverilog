// Normal Bind
bind fifo fifo_sva fifo_sva_inst (.clk(clk_i ),.rst_n(rst_n_i),.data_i(data_i),.data_o(data_o),.wr(wr_i),.rd(rd_i));

// Bind using Implicit port connections
bind fifo fifo_sva fifo_sva_inst(.*);

// Bind to a lower level module
bind $root.vhdl_top.sub1_inst.sub2_inst slave_sva_check slave_bind(/*..*/);  //Design with vhdl top (in IFV tool)

// Bind using different parameters/generic
bind fifo fifo_sva #(.wordsize (8),.fifosize (32) )
                      fifo_sva_inst (.clk(clk_i ),.rst_n(rst_n_i),
                                     .data_i(data_i),.data_o(data_o),
                 .wr(wr_i),.rd(rd_i));

// Bind to a instance of a module
bind fifo: fifo1, fifo2 fifo_sva fifo_sva_inst2 (.clk(clk_i ),.rst_n(rst_n_i),.data_i(data_i),.data_o(data_o),.wr(wr_i),.rd(rd_i));

bind fifo: fifo1 fifo_sva fifo_sva_inst1 (.clk(clk_i ),.rst_n(rst_n_i),.data_i(data_i),.data_o(data_o),.wr(wr_i),.rd(rd_i));  //binding to only fifo1 inst
