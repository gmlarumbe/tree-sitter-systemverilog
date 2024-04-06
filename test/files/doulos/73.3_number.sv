// Section 73.3: Number

// Illegal numbers for the reasons given:
int a = _23;                // Begins with _
int a = 8' HF F;                // Contains two illegal spaces
int a = 0ae;                // Decimal number with hex digits
int a = x;                  // A name, not a number (use 1'bx)
int a = .17;                // Should be 0.17


