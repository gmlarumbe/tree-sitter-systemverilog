// LRM 33.4.2

config bot;
    design lib1.bot;
    default liblist lib1 lib2;
    instance bot.a1 liblist lib3;
endconfig

config top;
    design lib1.top;
    default liblist lib2 lib1;
    instance top.bot use lib1.bot:config;
    instance top.bot.a1 liblist lib4;
    // ERROR - cannot set liblist for top.bot.a1 from this config
endconfig

config cfgl;
    design rtlLib.top;
    instance top use #(.WIDTH(32));
    instance top.a1 use #(.W(top.WIDTH));
endconfig

config cfg2;
    localparam S = 24;
    design rtlLib.top4;
    instance top4.a1 use #(.W(top4.S));
    instance top4.a2 use #(.W(S));
endconfig
