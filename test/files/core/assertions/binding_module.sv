//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Binding File 
//+++++++++++++++++++++++++++++++++++++++++++++++++
module binding_module();
//=================================================
// Bind by Module name : This will bind all instance
// of DUT
//=================================================
// Here RTL : stands for design under test
//      VIP : Assertion file
//   RTL Module Name  VIP module Name   Instance Name
bind bind_assertion   assertion_ip      U_assert_ip (
// .vip port (RTL port)
 .clk_ip   (clk),
 .req_ip   (req),
 .reset_ip (reset),
 .gnt_ip   (gnt)
);
//=================================================
// Bind by instance name : This will bind only instance
//  names in list
//=================================================
// Here RTL : stands for design under test
//      VIP : Assertion file
//     RTL Module Name Instance Path               VIP module Name Instance Name
//bind bind_assertion :$root.bind_assertion_tb.dut assertion_ip    U_assert_ip (
// .vip port (RTL port)
// .clk_ip   (clk),
// .req_ip   (req),
// .reset_ip (reset),
// .gnt_ip   (gnt)
//);
//=================================================

endmodule
