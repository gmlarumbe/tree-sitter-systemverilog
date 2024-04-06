// Section 136.1: Throughout

property p;
$fell(burst_mode) ##0
  (!burst_mode) throughout (##2((trdy==0)&&(irdy==0)) [*4]);
endproperty

