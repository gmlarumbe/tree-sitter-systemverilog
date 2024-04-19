//+++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++
module subroutine_assertion();

logic clk = 0;
always #1 clk ++;

logic [7:0] portin, portout;
logic       in_en, out_en;
//=================================================
// Sequence Layer
//=================================================
sequence local_var_seq;
   logic [7:0] lport;
   (in_en, lport = portin) ##[1:5] 
      (out_en and lport == portout, 
        $display ("@%0dns Input port %0d and Output port %0d match", 
         $time, lport,portout));
endsequence
//=================================================
// Property Specification Layer
//=================================================
property local_var_prop;
  @ (posedge clk) 
      in_en |-> local_var_seq;
endproperty
//=================================================
// Assertion Directive Layer
//=================================================
local_var_assert : assert property (local_var_prop);
//=================================================
// Simple DUT logic 
//=================================================
always @ (posedge clk)
begin
  portout <= (portin < 4) ? portin : portin + 1;
  out_en  <= in_en;
end
//=================================================
// Generate input vectors
//=================================================
initial begin
  in_en <= 0; out_en <= 0;
  portin <= 0; portout <= 0;
  repeat (20) @ (posedge clk);
  for (int i =0 ; i < 8; i ++) begin
    @ (posedge clk);
    in_en <= 1;
    portin <= i;
    @ (posedge clk);
    in_en <= 0;
    portin <= 0;
  end
  #30 $finish;
end

endmodule
