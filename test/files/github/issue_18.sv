assign a = (a);
assign a = (a.a);
assign a = (a.a[a]);
assign a = (a.a[a.a]);
assign a = a.a[a.a[a]]; // ERROR
assign a = (a.a[a.a[a]]); // ERROR
assign a = a.a[a.a[a]];
assign a = (a[a.a[a]]);
assign a = (a.a[a[a]]);
assign a = (a.a[a.a]);
assign a = (a.a.a.a);
assign a = (a.a[a.a.a.a]);

assign a = (a.a[a] == a[a::a-1:0]); // ERROR
assign a = a.a[a] == a[a::a-1:0];
assign a = (a.a[a] == a[a-1:0]);
assign a = (a[a] == a[a::a-1:0]);
assign a = a.a == a[a::a-1:0];
// assign a = (a.a == a[a::a-1:0]);
assign a = (a.a[a] != a[a::a-1:0]); //ERROR
assign a = (a[a::a-1:0]);
assign a = (a.a[a]);
assign a = (a.a[a] == a[a::a:0]);
assign a = (a.a[a] == a[a::a-1]);
