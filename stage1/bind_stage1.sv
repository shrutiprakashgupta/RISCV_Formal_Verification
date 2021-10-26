module bind_stage1 (
logic        clk_i,
logic        reset_i,
logic [31:0] irdata_i,      
logic        branch_taken_w,
logic [31:0] jump_addr_w,  
logic        ex_stall_w,
 
logic [31:0] id_pc_r,
logic [31:0] id_next_pc_r,
logic  [4:0] id_rd_index_r,
logic  [4:0] addr_1,
logic  [4:0] addr_2,
logic        id_a_signed_r,
logic        id_b_signed_r,
logic  [3:0] id_alu_op_r,
 
logic [31:0] id_imm_r,
logic        id_op_imm_r,
 
logic        id_mem_rd_r,
logic        id_mem_wr_r,
logic        id_mem_signed_r,
logic  [1:0] id_mem_size_r,
 
logic  [2:0] id_branch_r,
logic        id_reg_jump_r,
 
logic [31:0] iaddr_o,
logic        ird_o
);

   stage1 uut_stage1 (.*);
   bind uut_stage1 tb_stage1 bind_uut_stage1 (.*);

endmodule
