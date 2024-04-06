module foo;
    initial  begin
        uvm_config_db::get(null, "", "some_type", m_some_type);
        uvm_config_db #(some_type)::get(null, "", "some_type", m_some_type);
        if(!uvm_config_db #(some_type)::get(null, "", "some_type", m_some_type)) begin
           `uvm_error(get_name(), $sformatf("Error! Couldn not find %s", m_some_type))
        end
    end
endmodule
