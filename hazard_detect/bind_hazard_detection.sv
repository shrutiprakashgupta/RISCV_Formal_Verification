module bind_hazard_detection (
   logic        clk_i,
   logic        reset_i,
   logic  [4:0] id_ra_index_w,
   logic  [4:0] id_rb_index_w,
   logic  [4:0] id_rd_index_r,
   logic  [4:0] ex_rd_index_r,
   logic  [4:0] mem_rd_index_w,

   logic [31:0] id_ra_value_r,
   logic [31:0] id_rb_value_r,
   logic [31:0] ex_alu_res_r,
   logic [31:0] mem_wb_alu_result_r,
   logic [31:0] mem_rdata_w,

   logic        mem_access_w,

   logic        ex_hazard_w_a,
   logic        ex_hazard_w_b,
   logic        mem_hazard_w_a,
   logic        mem_hazard_w_b,
   logic [31:0] rd_value_r,      
   logic [31:0] exe_ra_r,      
   logic [31:0] exe_rb_r      
);

   hazard_detection uut_hazard_detection (.*);
   bind uut_hazard_detection tb_hazard_detection bind_uut_hazard_detection (.*);
endmodule 
