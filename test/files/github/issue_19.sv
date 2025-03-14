 localparam logic [CVA6Cfg.XLEN-1:0] IsaCode = (CVA6Cfg.XLEN'(CVA6Cfg.RVA) <<  0)                // A - Atomic Instructions extension
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVB) << 1)  // B - Bitmanip extension
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVC) << 2)  // C - Compressed extension
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVD) << 3)  // D - Double precision floating-point extension
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVF) << 5)  // F - Single precision floating-point extension
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVH) << 7)  // H - Hypervisor extension
 | (CVA6Cfg.XLEN'(1) << 8)  // I - RV32I/64I/128I base ISA
 | (CVA6Cfg.XLEN'(1) << 12)  // M - Integer Multiply/Divide extension
 | (CVA6Cfg.XLEN'(0) << 13)  // N - User level interrupts supported
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVS) << 18)  // S - Supervisor mode implemented
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVU) << 20)  // U - User mode implemented
 | (CVA6Cfg.XLEN'(CVA6Cfg.RVV) << 21)  // V - Vector extension
 | (CVA6Cfg.XLEN'(CVA6Cfg.NSX) << 23)  // X - Non-standard extensions present
 | ((CVA6Cfg.XLEN == 64 ? 2 : 1) << CVA6Cfg.XLEN - 2);  // MXL
