// Section 31.1: Dynamic Array

logic [7:0] array [];            // Declare a dynamic array
array = new[100];                // Create an array of100 elements
array = new[200](array);         // Double the size, preserving the existing elements
$display("array has %d elements", array.size());
array.delete();                  // Array now has no elements


