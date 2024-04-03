// Section 55.5: Instantiation

//The following example shows an array of instances
module Tristate8 (out, in, ena);
  output [7:0] out;
  input [7:0] in;
  input ena;

  bufif1 U1[7:0] (out, in, ena);

/* Equivalent (except the instance names) to /*...*/
  bufif1 U1_7 (out[7], in[7], ena);
  bufif1 U1_6 (out[6], in[6], ena);
  bufif1 U1_5 (out[5], in[5], ena);
  bufif1 U1_4 (out[4], in[4], ena);
  bufif1 U1_3 (out[3], in[3], ena);
  bufif1 U1_2 (out[2], in[2], ena);
  bufif1 U1_1 (out[1], in[1], ena);
  bufif1 U1_0 (out[0], in[0], ena);

endmodule


