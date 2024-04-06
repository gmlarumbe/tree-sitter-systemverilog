// Section 90.1: Semaphore

semaphore sm = new(2);  // Create semaphore with 2 keys
sm.get();               // Get a key, or block if none available
sm.put(2);              // Return two keys


