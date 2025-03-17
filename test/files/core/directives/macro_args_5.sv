  `define CONNECT_RVFI_FULL(CSR_ENABLE_COND, CSR_NAME,
                            CSR_SOURCE_NAME) \
    always_ff @(posedge clk_i) begin \
        if (CSR_ENABLE_COND) begin \
            rvfi_csr_o.``CSR_NAME``.rdata <= {{CVA6Cfg.XLEN - $bits(CSR_SOURCE_NAME)}, CSR_SOURCE_NAME}; \
        end \
    end \
    assign rvfi_csr_o.``CSR_NAME``.wdata = CSR_ENABLE_COND ? { {{CVA6Cfg.XLEN-$bits(CSR_SOURCE_NAME)}, CSR_SOURCE_NAME} } : 0; \
    assign rvfi_csr_o.``CSR_NAME``.rmask = CSR_ENABLE_COND ? 1 : 0; \
    assign rvfi_csr_o.``CSR_NAME``.wmask = (rvfi_csr_o.``CSR_NAME``.rdata != {{CVA6Cfg.XLEN - $bits(CSR_SOURCE_NAME)}, CSR_SOURCE_NAME}) && CSR_ENABLE_COND;
