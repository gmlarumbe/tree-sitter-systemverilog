// hierarchical identifier with non-constant expressions (i++) plus select plus part select
function f;
    left.member[i++].nested[1][2][1:0] = right.member[i++].nested[1][2][1:0];
endfunction
