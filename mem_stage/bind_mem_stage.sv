module bind_mem_stage (
   logic        clk_i,
   logic        reset_i,
   logic [31:0] ex_alu_res_r, 
   logic [31:0] ex_mem_data_r,
   logic        ex_mem_rd_r,
   logic        ex_mem_wr_r,
   logic        ex_mem_signed_r,
   logic  [1:0] ex_mem_size_r,
   logic [31:0] drdata_i,
   logic  [4:0] ex_rd_index_w,
                               
   logic  [4:0] mem_rd_index_w,
   logic [31:0] mem_wb_alu_result_r,
   logic [31:0] daddr_o,
   logic [31:0] dwdata_o,
   logic  [1:0] dsize_o,
   logic        drd_o,
   logic        dwr_o,
   logic [31:0] mem_rdata_for_hazard,
   logic        mem_access_w,
 
   logic [31:0] mem_rdata_w,
   logic  [3:0] dbe_w

);
   mem_stage uut_mem_stage (.*);
   bind uut_mem_stage tb_mem_stage bind_uut_mem_stage (.*);

endmodule
