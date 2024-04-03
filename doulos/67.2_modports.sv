// Section 67.2: Modports

// Hierarchical interface:
interface Intf;
  interface FPGAtoDSPInt;
    /*...*/
    modport Master(input a/*...*/);
    modport Slave (output a/*...*/);
    /*...*/
  endinterface: FPGAtoDSPInt
  FPGAtoDSPInt Intf1, Intf2;
  // modport Master2 (Intf1.Master, Intf2.Master); // INFO: Not supported by most tools
endinterface


