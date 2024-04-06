// Section 7.1: Associative Array

// Create an array of integer, indexed by string
integer CountWords [string];
CountWords["one"]++;
$display("There are %0d different words", CountWords.num);
CountWords.delete("one");              // Deletes the "one" entry
CountWords.delete;                     // Clears the entire array


