virtual class TLM_channel_base #(type Tr = Transaction, C = Component)
  implements Messaging #(Tr), Connecting #(C);

  protected event e_get, e_put;
  protected int bound;

  pure virtual protected function T pop();
  pure virtual protected function void push(T t);

endclass : TLM_channel_base
