//+++++++++++++++++++++++++++++++++++++++++++++++++
//   Assertion Verification IP
//+++++++++++++++++++++++++++++++++++++++++++++++++
module assertion_ip(input wire clk_ip, req_ip,reset_ip,gnt_ip);
//=================================================
// Sequence Layer
//=================================================
sequence req_gnt_seq;
  (~req_ip & gnt_ip) ##1 (~req_ip & ~gnt_ip);
endsequence
//=================================================
// Property Specification Layer
//=================================================
property req_gnt_prop;
  @ (posedge clk_ip) 
    disable iff (reset_ip)
      req_ip |=> req_gnt_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
req_gnt_assert : assert property (req_gnt_prop)
                 else
                 $display("@%0dns Assertion Failed", $time);

endmodule
