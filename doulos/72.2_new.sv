// Section 72.2: New

// Dynamic arrays
initial begin
string Names[] = new[20];       // 20 elements

Names = new[40] (Names);        // Expand to 40 elements;
                                // preserviing the first 20
                                // elements.

Names = new[30];                // Resize to 30 elements.
                                // Initialize all elements to
                                // default value of the
                                // element datatype.

end
