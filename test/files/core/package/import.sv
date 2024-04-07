import pkg::*;

module package_example;
  initial begin
    transaction tr = new();
    tr.display();
    pkg_funct();
  end
endmodule
