covergroup foo_cg;
 label : cross cp1, cp2 {
        bins b0 = binsof(cp1) intersect {0} && binsof(cp2) intersect {0};
        bins b1 = binsof(cp1) intersect {0} && binsof(cp2) intersect {1};
        bins b2 = binsof(cp1) intersect {0} && binsof(cp2) intersect {2};
        bins b3 = binsof(cp1) intersect {0} && binsof(cp2) intersect {3};
 }
endgroup
