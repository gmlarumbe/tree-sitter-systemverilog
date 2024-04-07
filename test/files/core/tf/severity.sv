initial begin
    $fatal(0, "Fatal with finish_number");
    $fatal(1, "Fatal with finish_number");
    $fatal(2, "Fatal with finish_number");
    $fatal(1, "Fatal with finish_number and 1 arg: %0d", arg);
    $fatal("Fatal without finish_number");
    $fatal("Fatal without finish_number and 1 arg: %0d", arg);
    $error("Error without args");
    $error("Error with arg: %0d", arg);
    $warning("Warning without args");
    $warning("Warning with arg: %0d", arg);
    $info("Info without args");
    $info("Info with arg: %0d", arg);
end
