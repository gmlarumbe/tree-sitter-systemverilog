// Section 23.2: Coverpoint

// Example showing bins and transitions
bit [5:0] V;
covergroup CG @(posedge clk);
  coverpoint V
  {
    bins a = {[0:3], 5};           // One bin for these values 
                                   // of V - 0, 1, 2, 3, or 5
    bins b[3] = {[6:11]};          // 3 bins: <6,7>,<8,9>,<10,11>
    bins c[2] = {[13:17]};         // 2 bins: <13,14>,<15,16,17>
    bins d[] = {18, 19};           // 2 bins: d[18], d[19]
    bins e[] = {[20:30], [25:40]}; // Overlapping values - OK
    bins f = (41 => 43), ([50:52],55=>56,57);
       // Associates the following sequences with bin f: 41=>43, or 50=>56, 
       // 51=>56, 52=>56, 55=>56, 50=>57, 51=>57, 52=>57, 55=>57
    bins h = {[60:$]}; // bin h: values from 60 to 63 ($ is max of V)
    ignore_bins ig_vals = {18, 19}; 
                       // ignores values, even though included in bin d
    illegal_bins ill_trans = (47 => 48 => 49); 
       // This sequence will produce a run-time eror
    wildcard bins wb = {5'b11??1}; // 11001 11011 11101 11111
    bins others[] = default;   
       // Any value not maching a, b[3], c[2], d[], e[], f, h, wb, etc.
  }
endgroup


