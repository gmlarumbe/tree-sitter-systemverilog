interface class Messaging #(type T = logic);
  pure virtual task          put(T t);
  pure virtual task          get(output T t);
  pure virtual task          peek(output T t);
  pure virtual function bit  try_peek(output T t);
  pure virtual function bit  try_put(T t);
  pure virtual function bit  try_get(output T t);
endclass
