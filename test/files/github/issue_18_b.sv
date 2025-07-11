assign a = a.a[a];
assign a = (a.a[a]);

assign a = a.a[a.a[a]];
assign a = (a.a[a.a[a]]); // ERROR

assign a = a.a[a.a[a.a[a]]]; // ERROR
assign a = (a.a[a.a[a.a[a]]]); // ERROR

assign a = a.a[a.a[a.a[a.a[a]]]]; // ERROR
assign a = (a.a[a.a[a.a[a.a[a]]]]); // ERROR
