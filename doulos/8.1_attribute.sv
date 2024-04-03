// Section 8.1: Attribute

initial begin
(*synthesis, parallel_case *) casez (Opcode)
  4'b??01 : action1;
  4'b1?0? : action2;
/*...*/
endcase
end

