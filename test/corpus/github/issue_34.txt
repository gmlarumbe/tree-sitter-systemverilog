assign a = (a.a == a[a::a-1:0]); // ERROR

assign a = (a.a == a[(a::a)-1:0]);
assign a = a.a == a[a::a-1:0];
assign a = (a.a[0] == a[a::a-1:0]);
assign a = a.a[0] == a[a::a-1:0];
assign a = (a.a[0] == a[(a::a)-1:0]);
assign a = (a.a[i] == a[a::a-1:0]);
assign a = (a == a[a::a-1:0]);
