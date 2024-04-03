// Section 45.1: Function

function [7:0] ReverseBits;
  input [7:0] Byte;
  integer i;
    for (i = 0; i < 8; i = i + 1)
      ReverseBits[7-i] = Byte[i];
endfunction


