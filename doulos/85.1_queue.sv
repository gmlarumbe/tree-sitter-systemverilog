// Section 85.1: Queue

initial begin
int Q1[$];                      // An empty queue of ints
int Q2[$] = '{1, 2};            // An initialised queue of ints
bit Q3[$:7];                    // A queue with max size = 8 bits

int I1, e;
I1 = Q2[0];                     // Read the first (left-most) item
I1 = Q2[$];                     // Read the last (right-most) item
Q2 = Q2[0:$-1];                 // Delete the last (right-most) item
Q2 = Q2[1:$-1];                 // Delete the first and last items
Q.delete(i);                     // Equiv. to: Q = '{Q[0:i-1], Q[i+1,$]}
Q1 = Q2;                        // Copy Q2 in Q1
Q2 = '{Q2, 3};                  // Insert 3 at the end
Q2 = '{Q2[0:i-1], j, Q2[i:$] }; // Insert j at position i
Q2 = '{Q2[0:i], j, Q2[i+1:$] }; // Insert j after position i
e = Q.pop_front();               // Equiv. to: e = Q[0]; Q = Q[1,$]
e = Q.pop_back();                // Equiv. to: e = Q[$]; Q = Q[0,$-1]
Q.push_front(e);                 // Equiv. to: Q = '{e, Q}
end
