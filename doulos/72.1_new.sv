// Section 72.1: New

class C;
  bit [3:0] size;

  covergroup cov_size;
    coverpoint size;
  endgroup

  function new(input j = 0);    // Class constructor
    size = j;
    cov_size = new;             // Covergroup instance
  endfunction
endclass

C c1, c2, c3;
C c4 = new;                     // Declare and initialize

module foo;
initial begin
  c1 = new;                     // Size = 0
  c2 = new(10);                 // Size = 10
  c3 = new c2;                  // Size = 10
  /*...*/
  repeat (20) begin
    c2.size = $urandom_range(0, 15);
    c2.cov_size.sample();
  end
  /*...*/
end
endmodule

