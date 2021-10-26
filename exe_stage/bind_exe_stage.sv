module bind_exe_stage (

logic        clk_i,
logic        reset_i,

logic  [3:0] id_alu_op_r,

logic [31:0] id_ra_value_r,
logic [31:0] id_rb_value_r,
logic        id_a_signed_r,
logic        id_b_signed_r,
logic  [4:0] id_rd_index_r,

logic [31:0] id_imm_r,
logic        id_op_imm_r,

logic [31:0] id_pc_reg,
logic [31:0] id_next_pc_r,
logic        id_reg_jump_r, 
logic  [2:0] id_branch_r,

logic        id_mem_rd_r,
logic        id_mem_wr_r,
logic  [1:0] id_mem_size_r,
logic        id_mem_signed_r,

logic        branch_taken_w,
logic [31:0] jump_addr_w,

logic  [4:0] ex_rd_index_r,
logic [31:0] ex_alu_res_r,
logic [31:0] ex_mem_data_r,
logic        ex_mem_rd_r,
logic        ex_mem_wr_r,
logic        ex_mem_signed_r,
logic  [1:0] ex_mem_size_r,

logic        ex_stall_w
);

   exe_stage uut_exe_stage (.*);
   bind uut_exe_stage tb_exe_stage bind_uut_exe_stage (.*);

endmodule
