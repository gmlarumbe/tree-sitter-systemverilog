// Section 32.1: Enum

// This example shows how some of the enumerated type methods are used.
enum States {Reset, Go1, Go2} State;

initial begin
  $display("The enum States has %0d values: ", State.num);
  State = State.first();
  do begin
    $display("  %s (%0d)", State.name, State);
    State = State.next;
  end while (State != State.first); // next() wraps at the end
end


