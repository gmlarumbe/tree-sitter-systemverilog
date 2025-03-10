initial begin
    // Illegal conversion from 24-bit struct to 32 bit int - compile-time error
    struct {bit[7:0] a; shortint b;} a;
    int b = int'(a);

    // Illegal conversion from 20-bit struct to int (32 bits) - run-time error
    struct {bit a[$]; shortint b;} a = '{'{0,1,0,1}, 67};
    int b = int'(a);
    // Illegal conversion from int (32 bits) to struct dest_t (25 or 33 bits), compile-time error
    typedef struct {byte a[$]; bit b;} dest_t;
    int a;
    dest_t b = dest_t'(a);
end
