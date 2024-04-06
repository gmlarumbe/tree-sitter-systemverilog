// Section 89.2: Repeat

initial begin
repeat  (3) @(EventExpr); // Will execute EventExpr 3 times.
repeat (-3) @(EventExpr); // Will not execute EventExpression.
repeat  (a) @(EventExpr); // If a is assigned -3, will execute the
                         // EventExpr once if a declared unsigned.
                         // Will not execute if a is signed.

end
