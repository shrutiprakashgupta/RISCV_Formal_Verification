`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Module Name: top
//////////////////////////////////////////////////////////////////////////////////

module top(
input         clk_i,
input         reset_i,

//Instruction memory signals
input [31:0] irdata_i,
output        ird_o,
output [31:0] iaddr_o,

//Hazard detection module signals
output [31:0] exe_ra_r,
output [31:0] exe_rb_r,

//Stage_1 signals
output [31:0] id_pc_r,
output [31:0] id_next_pc_r,
output  [4:0] id_rd_index_r,
output  [4:0] addr_1,
output  [4:0] addr_2,
output [31:0] id_imm_r,
output        id_a_signed_r,
output        id_b_signed_r,
output        id_op_imm_r,
output  [3:0] id_alu_op_r,
output        id_mem_rd_r,
output        id_mem_wr_r,
output        id_mem_signed_r,
output  [1:0] id_mem_size_r,
output  [2:0] id_branch_r,
output        id_reg_jump_r,
output        branch_taken_w,
output [31:0] jump_addr_w,
output 		  ex_stall_w,

//Execute stage signals 
output  [4:0] ex_rd_index_r,
output [31:0] ex_alu_res_r,
output [31:0] ex_mem_data_r,
output        ex_mem_rd_r,
output        ex_mem_wr_r,
output        ex_mem_signed_r,
output  [1:0] ex_mem_size_r,

output  [4:0] mem_rd_index_w,
output [31:0] mem_wb_alu_result_r,
output        mem_access_w,
output [31:0] mem_rdata_w,
output [31:0] mem_rdata_for_hazard,

////Data Memory module signals
output [31:0] daddr_o,
output [31:0] dwdata_o,
input [31:0] drdata_i,
output  [1:0] dsize_o,
output  [3:0] dbe_w,
output        drd_o,
output        dwr_o,

//Write back stage signals
output [31:0] rd_value_w,

//Register file signals 
output [31:0] id_ra_value_r,
output [31:0] id_rb_value_r

);

//instruction_memory instruction_memory_from_top(
//	.clk_i(clk_i),
//	.reset_i(reset_i),
//	
//	.iaddr_i(iaddr_o),
//	
//	.ird_i(ird_o),
//	.irdata_o(irdata_i)
//);

hazard_detection hazard_detection_from_top(
	.reset_i(reset_i),
	
	.id_ra_index_w(addr_1),
	.id_rb_index_w(addr_2),
	.id_rd_index_r(id_rd_index_r),
	.ex_rd_index_r(ex_rd_index_r),
	.mem_rd_index_w(mem_rd_index_w),
	.id_ra_value_r(id_ra_value_r),
	.id_rb_value_r(id_rb_value_r),
	.ex_alu_res_r(ex_alu_res_r),
	.mem_wb_alu_result_r(mem_wb_alu_result_r),
	.mem_rdata_w(mem_rdata_for_hazard),
	.mem_access_w(mem_access_w),
	
	.exe_ra_r(exe_ra_r),
	.exe_rb_r(exe_rb_r)
);

stage1 if_id_from_top(
	.clk_i(clk_i),
	.reset_i(reset_i),
	
	.irdata_i(irdata_i),
	.id_branch_r(id_branch_r),
	.id_reg_jump_r(id_reg_jump_r),
	.ex_stall_w(ex_stall_w),
	
	.id_pc_r(id_pc_r),
	.id_next_pc_r(id_next_pc_r),
	
	.addr_1(addr_1),
	.addr_2(addr_2),
	.id_rd_index_r(id_rd_index_r),
	
	.id_alu_op_r(id_alu_op_r),
	.id_a_signed_r(id_a_signed_r),
	.id_b_signed_r(id_b_signed_r),
	
	.id_op_imm_r(id_op_imm_r),
	.id_imm_r(id_imm_r),
	
	.id_mem_rd_r(id_mem_rd_r),
	.id_mem_wr_r(id_mem_wr_r),
	.id_mem_signed_r(id_mem_signed_r),
	.id_mem_size_r(id_mem_size_r),
	
	.branch_taken_w(branch_taken_w), 
	.jump_addr_w(jump_addr_w), 
	
	.iaddr_o(iaddr_o),
	.ird_o(ird_o)
);

exe_stage exe_Stage_from_top(
	.clk_i(clk_i),
	.reset_i(reset_i),
	
	.id_alu_op_r(id_alu_op_r),
	.id_op_imm_r(id_op_imm_r),
	.id_a_signed_r(id_a_signed_r),
	.id_b_signed_r(id_b_signed_r),
	
	.id_ra_value_r(exe_ra_r),
	.id_rb_value_r(exe_rb_r),
	.id_imm_r(id_imm_r),
	.id_rd_index_r(id_rd_index_r),
	
	.id_pc_reg(id_pc_r),
	.id_next_pc_r(id_next_pc_r),
	.id_branch_r(id_branch_r),
	.id_reg_jump_r(id_reg_jump_r),
	
	.id_mem_rd_r(id_mem_rd_r),
	.id_mem_wr_r(id_mem_wr_r),
	.id_mem_signed_r(id_mem_signed_r),
	.id_mem_size_r(id_mem_size_r),
	
	.ex_rd_index_r(ex_rd_index_r),
	.ex_alu_res_r(ex_alu_res_r),
	
	.ex_mem_data_r(ex_mem_data_r),
	.ex_mem_rd_r(ex_mem_rd_r),
	.ex_mem_wr_r(ex_mem_wr_r),
	.ex_mem_signed_r(ex_mem_signed_r),
	.ex_mem_size_r(ex_mem_size_r),
	
	.branch_taken_w(branch_taken_w),
	.jump_addr_w(jump_addr_w),
	.ex_stall_w(ex_stall_w)
);
      
mem_stage mem_stage_from_top(
	.clk_i(clk_i),
	.reset_i(reset_i),
	
	.ex_alu_res_r(ex_alu_res_r),
	.ex_mem_data_r(ex_mem_data_r),
	.ex_mem_rd_r(ex_mem_rd_r),
	.ex_mem_wr_r(ex_mem_wr_r),
	.ex_mem_signed_r(ex_mem_signed_r),
	.ex_mem_size_r(ex_mem_size_r),
	.drdata_i(drdata_i),
	        
	.ex_rd_index_w(ex_rd_index_r),
	        
	.mem_rd_index_w(mem_rd_index_w),
	.mem_wb_alu_result_r(mem_wb_alu_result_r),
	.mem_access_w(mem_access_w),
	.mem_rdata_w(mem_rdata_w),
	
	.daddr_o(daddr_o),
	.dwdata_o(dwdata_o),
	.dsize_o(dsize_o),
	.drd_o(drd_o),
	.dwr_o(dwr_o),
	.dbe_w(dbe_w),
	.mem_rdata_for_hazard(mem_rdata_for_hazard)
);

//memory data_memory(
//	.clk_i(clk_i),
//	.reset_i(reset_i),
//	
//	.daddr_i(daddr_o),
//	.dwdata_i(dwdata_o),
//	.drdata_o(drdata_i),
//	.dsize_i(dsize_o),
//	.drd_i(drd_o),
//	.dwr_i(dwr_o),  
//	.dbe_w(dbe_w)
//);
    
assign rd_value_w = mem_access_w ? mem_access_w : mem_wb_alu_result_r; 

register_file register_file_from_top(
	.clk_i(clk_i),
	.reset_i(reset_i),
	
	.addr_1(addr_1),
	.addr_2(addr_2),
	
	.out_1(id_ra_value_r),
	.out_2(id_rb_value_r),
	
	.data_in(rd_value_w),
	.data_write_address(mem_rd_index_w),
	.write_enable_w(1'b1)
);

endmodule
