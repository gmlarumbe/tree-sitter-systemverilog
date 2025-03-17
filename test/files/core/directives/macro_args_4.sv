`define uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null)   \
begin                                                           \
  uvm_resource#(TYPE) __tmp_rsrc__;                             \
  SUCCESS = $cast(__tmp_rsrc__, RSRC);                          \
  if (SUCCESS) begin                                            \
    VAL = __tmp_rsrc__.read(OBJ);                               \
  end                                                           \
end

