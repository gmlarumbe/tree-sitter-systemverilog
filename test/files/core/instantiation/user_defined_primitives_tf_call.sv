module foo;
    my_and (Q, A, B);
    my_and (pull0, strong1) (Q, A, B);

    initial begin
        // The one below should be parsed as a tf_call
        my_and (Q, A, B);
    end
endmodule
