// Section 147.1: $typename

package a_pkg;
  enum {INIT, START, RUNNING, STOP = 5} state;
endpackage

module m;
  import a_pkg::*;
  typedef logic [15:1] word_t;
  struct {bit s; bit [14:0] m;} arr[];
  string s = $typename(word_t);
  word_t wdata;

  initial begin
    $display($typename(state));
    $display($typename(word_t));
    $display($typename(wdata));
    $display($typename(arr));
    $display($typename(s));
  end
endmodule


