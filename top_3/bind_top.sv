module bind_top (
logic         clk_i,
logic         reset_i,

//Instruction memory signals
logic [31:0] irdata_i,
logic        ird_o,
logic [31:0] iaddr_o,

//Hazard detection module signals
logic [31:0] exe_ra_r,
logic [31:0] exe_rb_r,

//Stage_1 signals
logic [31:0] id_pc_r,
logic [31:0] id_next_pc_r,
logic  [4:0] id_rd_index_r,
logic  [4:0] addr_1,
logic  [4:0] addr_2,
logic [31:0] id_imm_r,
logic        id_a_signed_r,
logic        id_b_signed_r,
logic        id_op_imm_r,
logic  [3:0] id_alu_op_r,
logic        id_mem_rd_r,
logic        id_mem_wr_r,
logic        id_mem_signed_r,
logic  [1:0] id_mem_size_r,
logic  [2:0] id_branch_r,
logic        id_reg_jump_r,
logic        branch_taken_w,
logic [31:0] jump_addr_w,
logic 		  ex_stall_w,

//Execute stage signals 
logic  [4:0] ex_rd_index_r,
logic [31:0] ex_alu_res_r,
logic [31:0] ex_mem_data_r,
logic        ex_mem_rd_r,
logic        ex_mem_wr_r,
logic        ex_mem_signed_r,
logic  [1:0] ex_mem_size_r,

logic  [4:0] mem_rd_index_w,
logic [31:0] mem_wb_alu_result_r,
logic        mem_access_w,
logic [31:0] mem_rdata_w,
logic [31:0] mem_rdata_for_hazard,

////Data Memory module signals
logic [31:0] daddr_o,
logic [31:0] dwdata_o,
logic [31:0] drdata_i,
logic  [1:0] dsize_o,
logic  [3:0] dbe_w,
logic        drd_o,
logic        dwr_o,

//Write back stage signals
logic [31:0] rd_value_w,

//Register file signals 
logic [31:0] id_ra_value_r,
logic [31:0] id_rb_value_r
);

   top uut_top (.*);
   bind uut_top tb_top bind_uut_top (.*);

endmodule
