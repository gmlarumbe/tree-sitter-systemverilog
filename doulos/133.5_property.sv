// Section 133.5: Property

// Case property
property delayExample(logic [1:0] del);
  case (del)
    2'b00 : a && b;
    2'b01 : a ##1 b;
    2'b10 : a ##2 b;
    2'b11 : a ##3 b;
    default : 0; // doesn't hold if x or z 
  endcase
endproperty   


