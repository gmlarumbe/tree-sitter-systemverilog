// Section 97.1: String

string s1;             // s1 is initially ""
string s2 = "This is a string literal. ";
string s3;

s1 = "So is this.";
s2 = {s2,s1};          // s2 is now "This is a string literal. So is this."
s3.itoa(100);
$display(s3);          // "100"
$display(s1.len);      // Returns 11


