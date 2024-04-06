// Section 86.3: Rand

// The scope randomize function ([std::]randomize)
initial begin
bit a, b;                // Variables with module scope
bit OK;
OK = randomize(a, b);    // Make a, b random variables
OK = randomize(a, b) with {a != b;};
end

