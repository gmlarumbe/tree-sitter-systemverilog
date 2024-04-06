// Section 91.2: Specify

//Pulse-Style and showcancelled
specify
  showcancelled Out1, Out2;
  pulsestyle_ondetect Out1, Out2;
  (A => Out1)=(2,3);
  (B => Out1)=(3,4);
  (B => Out2)=(3,4);
  (B => Out2)=(5,6);
endspecify


