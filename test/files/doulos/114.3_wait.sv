// Section 114.3: Wait
  
// Wait until the events e1, e2 and e3 are triggered in that sequence.
// When this happens, success is set to one.
// If the events trigger out of sequence, success is set to 0.
wait_order (e1, e2, e3) success = 1; else success = 0;


