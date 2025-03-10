initial begin
    typedef struct {
        bit isfloat;
        union { int i; shortreal f; } n; // anonymous type
    } tagged_st;                         // named structure

    typedef bit [$bits(tagged_st) - 1 : 0] tagbits; // tagged_st defined above

    tagged_st a [7:0]; // unpacked array of structures

    tagbits t = tagbits'(a[3]); // convert structure to array of bits
    a[4] = tagged_st'(t); // convert array of bits back to structure
end
