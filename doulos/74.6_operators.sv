// Section 74.6: Operators

// Pack/unpack streaming operations
int x, y, z;
logic [3:0] v [2:0];
logic [4:1] w1, w2, w3;
bit [96:1] a = {>>{x, y, z}};    // Pack x, y, z, each 32 bits
bit [100:0] c = {>>{ x, y, z }}; // c is padded with 5 bits
{>>{x, y, z}} = 96'b111;         // Unpack x = 0, y = 0, z = 7
{>>{w1, w2, w3}} = v;            // w1 = v[2], w2 = v[1], w3 = v[0]
int b = {>>{x, y, z}};           // Error: b is 32 bits < 96 bits


