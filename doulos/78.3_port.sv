// Section 78.3: Port

typedef struct {
  bit A;
  // union {int i, real j} B; // Syntax error in most tools
} Struct1;

module M1 (input int In, output var Struct1 Out);
  /*...*/
endmodule


