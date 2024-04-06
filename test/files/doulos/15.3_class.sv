// Section 15.3: Class

// Parameterised classes
class Register #(parameter n = 8);
  logic [n-1:0] data;
  /*...*/
endclass

Register #(8) accum8 = new;           // 8-bit register
Register #(.n(16)) accum16 = new;     // 16-bit register

class Register #(parameter type T);
  T data;
  /*...*/
endclass

Register #(int) accum8 = new;         // int register
Register #(bit [7:0]) accum16 = new;  // bit[7:0] register


