covergroup foo_cg;
    option.per_instance = 1;
    label: coverpoint foo_cp {
        bins foo_bins = {};
        bins foo_bins = {[0:7]};
        bins foo_bins[] = {};
        bins foo_bins[] = {[0:7]};
        bins foo_bins[] = default;
    }
endgroup
