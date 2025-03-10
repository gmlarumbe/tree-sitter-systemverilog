initial begin
    typedef enum {red, green, blue, yellow, white, black} Colors;
    Colors col;
    $cast(col, 2 + 3);

    if (! $cast(col, 2 + 8)) // 10: invalid cast
        $display("Error in cast");
end
