`define uvm_do(SEQ_OR_ITEM, SEQR=get_sequencer(), PRIORITY=-1, CONSTRAINTS={}) \
  begin \
  `uvm_create(SEQ_OR_ITEM, SEQR) \
  `uvm_rand_send(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS) \
  end
