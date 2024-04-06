// Section 22.2: Covergroup

// Setting options and type options procedurally after instantiating a covergroup 
covergroup CG @(posedge clk);
  CP1 : coverpoint A;
  CP2 : coverpoint B;
endgroup
CG C1 = new;
C1.option.comment = "A comment set for the instance C1";
C1.CP1.option.auto_bin_max = 8;  // Create 8 automatic bins for 
                                 // coverpoint CP1 of instance C1
CG::type_option.comment = "A comment set for C1";
CG::CP1::type_option.weight = 10;


