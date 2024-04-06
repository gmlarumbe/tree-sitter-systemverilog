// Section 78.4: Port

// Interface ports
interface Interf (input Clk);
  /*...*/
endinterface

module foo (Interf Int1 /*...*/);
  /*...*/
endmodule

module foo (interface Int2 /*...*/);   // Generic interface
  /*...*/
endmodule



