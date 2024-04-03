// Section 65.1: Mailbox

mailbox mbox = new;
string message;

mbox.put("This is a message");
mbox.get(message);  // Message now contains "This is a message"


