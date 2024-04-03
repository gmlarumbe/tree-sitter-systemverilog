// Section 107.3: Union

typedef union tagged packed {
  void Invalid;
  int i;
} IntOrInvalid;


IntOrInvalid ti;

module foo;
    initial begin
        ti = tagged i 42;                   // Tagged union expression
        ti.i = 10;                           // OK - tag is "i"
        if (ti.i == 10 ) begin end /*...*/                // True
        ti = tagged Invalid;                // No value needed
        if (ti.i == 10 ) begin /*...*/                // Error - ti is "Invalid"
        end
    end
endmodule

