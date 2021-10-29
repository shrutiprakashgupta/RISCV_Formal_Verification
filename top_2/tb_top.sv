module tb_top (
input         clk_i,
input         reset_i,

//Instruction memory signals
input [31:0] irdata_i,
input        ird_o,
input [31:0] iaddr_o,

//Hazard detection module signals
input [31:0] exe_ra_r,
input [31:0] exe_rb_r,

//Stage_1 signals
input [31:0] id_pc_r,
input [31:0] id_next_pc_r,
input  [4:0] id_rd_index_r,
input  [4:0] addr_1,
input  [4:0] addr_2,
input [31:0] id_imm_r,
input        id_a_signed_r,
input        id_b_signed_r,
input        id_op_imm_r,
input  [3:0] id_alu_op_r,
input        id_mem_rd_r,
input        id_mem_wr_r,
input        id_mem_signed_r,
input  [1:0] id_mem_size_r,
input  [2:0] id_branch_r,
input        id_reg_jump_r,
input        branch_taken_w,
input [31:0] jump_addr_w,
input 		  ex_stall_w,

//Execute stage signals 
input  [4:0] ex_rd_index_r,
input [31:0] ex_alu_res_r,
input [31:0] ex_mem_data_r,
input        ex_mem_rd_r,
input        ex_mem_wr_r,
input        ex_mem_signed_r,
input  [1:0] ex_mem_size_r,

input  [4:0] mem_rd_index_w,
input [31:0] mem_wb_alu_result_r,
input        mem_access_w,
input [31:0] mem_rdata_w,
input [31:0] mem_rdata_for_hazard,

////Data Memory module signals
input [31:0] daddr_o,
input [31:0] dwdata_o,
input [31:0] drdata_i,
input  [1:0] dsize_o,
input  [3:0] dbe_w,
input        drd_o,
input        dwr_o,

//Write back stage signals
input [31:0] rd_value_w,

//Register file signals 
input [31:0] id_ra_value_r,
input [31:0] id_rb_value_r

);

	//------------------------------------------------irdata_i----------------------------------------------------
	//Valid Instruction types
	property instr_types;
		@(posedge clk_i) disable iff (reset_i) irdata_i[6:0] inside 
		{7'b1100011, 7'b0000011, 7'b0100011, 7'b0010011, 7'b0110011, 7'b0110111, 7'b0010111, 7'b1101111, 7'b1100111};
	endproperty
	
	valid_instr_types: assume property (instr_types); 
	
	//Valid function7 types
	property f7_types;
		@(posedge clk_i) disable iff (reset_i) irdata_i[31:25] inside {7'b0000000, 7'b0100000, 7'b0000001};
	endproperty
	
	valid_f7_types: assume property (f7_types); 
	
	//B-type
	property b_type;
		@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b1100011) 
												|-> !(irdata_i[14:12] inside {3'b010, 3'b011});
	endproperty
	
	valid_btype_instr: assume property (b_type);
	
	//L-type
	property l_type;
		@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0000011) |-> !(irdata_i[14:12] inside {3'b011, 3'b110, 3'b111});
	endproperty
	
	valid_ltype_instr: assume property (l_type);
	
	//S-type
	property s_type;
		@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0100011) |-> (irdata_i[14:12] < 3'b011);
	endproperty
	
	valid_stype_instr: assume property (s_type);
	 
	//I-type
	property i_type1;
		@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0010011) && (irdata_i[14:12] == 3'b001) 
												|->	(irdata_i[31:25] == 7'b0000000);
	endproperty
	
	valid_itype1_instr: assume property (i_type1);
	
	property i_type2;
		@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0010011) && (irdata_i[14:12] == 3'b101) 
												|->	(irdata_i[31:25] != 7'b0000001);
	endproperty
	
	valid_itype2_instr: assume property (i_type2);
   
	//R-type - Very difficult to restrict the space to only supported
	//property r_type1;
	//	@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0110011) && (irdata_i[31:25] == 7'b0000000) //main 
	//											|->	All allowed;
	//endproperty
	
	//valid_rtype1_instr: assume property (r_type1);

	property r_type2;
		@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0110011) && (irdata_i[31:25] == 7'b0100000) //alt 
												|->	(irdata_i[14:12] inside {3'b000, 3'b101});
	endproperty
	
	valid_rtype2_instr: assume property (r_type2);
	
	//property r_type3;
	//	@(posedge clk_i) disable iff (reset_i) (irdata_i[6:0] == 7'b0110011) && (irdata_i[31:25] = 7'b0000001) //mul 
	//											|->	All Allowed;
	//endproperty
	
	//valid_rtype3_instr: assume property (r_type3);
  
	//IF Stage stall
	property if_stall;
		@(posedge clk_i) disable iff (reset_i) (iaddr_o == $past(iaddr_o)) |-> (irdata_i == $past(irdata_i));
	endproperty

	prop_if_stall: assume property (if_stall);

	//-----------------------------------------------drdata_i----------------------------------------------------
	//Zero value from memory while no read is performed 
	property no_data_if_no_read;
		@(posedge clk_i) disable iff (reset_i) (!drd_o) |-> (drdata_i == 32'b0);
	endproperty

	valid_data_on_read: assume property (no_data_if_no_read);
	
	//***************************************Checking output - Assertions**************************************** 
	//Dependency on execute
	property ex_hazard_a;
	   @(posedge clk_i) disable iff (reset_i) ((addr_1 == ex_rd_index_r) && (addr_1 != 5'd0)) |-> (exe_ra_r == ex_alu_res_r);
	endproperty
	
	prop_ex_hazard_a: assert property (ex_hazard_a);
	
	//Dependency on memorystage - without memory access
	property mem_n_access_hazard_a;
	   @(posedge clk_i) disable iff (reset_i) ((addr_1 != ex_rd_index_r) && (addr_1 == mem_rd_index_w) && (!mem_access_w) && (addr_1 != 5'd0)) |-> (exe_ra_r == mem_wb_alu_result_r);
	endproperty
	
	prop_mem_n_access_hazard_a: assert property (mem_n_access_hazard_a);
	
	//Dependency on memorystage - with memory access
	property mem_access_hazard_a;
	   @(posedge clk_i) disable iff (reset_i) ((addr_1 != ex_rd_index_r) && (addr_1 == mem_rd_index_w) && (mem_access_w) && (addr_1 != 5'd0)) |-> (exe_ra_r == mem_rdata_w);
	endproperty
	
	prop_mem_access_hazard_a: assert property (mem_access_hazard_a);
	
	//Dependency on execute
	property ex_hazard_b;
	   @(posedge clk_i) disable iff (reset_i) ((addr_2 == ex_rd_index_r) && (addr_2 != 5'd0)) |-> (exe_rb_r == ex_alu_res_r);
	endproperty
	
	prop_ex_hazard_b: assert property (ex_hazard_b);
	
	//Dependency on memorystage - without memory access
	property mem_n_access_hazard_b;
	   @(posedge clk_i) disable iff (reset_i) ((addr_2 != ex_rd_index_r) && (addr_2 == mem_rd_index_w) && (!mem_access_w) && (addr_2 != 5'd0)) |-> (exe_rb_r == mem_wb_alu_result_r);
	endproperty
	
	prop_mem_n_access_hazard_b: assert property (mem_n_access_hazard_b);
	
	//Dependency on memorystage - with memory access
	property mem_access_hazard_b;
	   @(posedge clk_i) disable iff (reset_i) ((addr_2 != ex_rd_index_r) && (addr_2 == mem_rd_index_w) && (mem_access_w) && (addr_2 != 5'd0)) |-> (exe_rb_r == mem_rdata_w);
	endproperty
	
	prop_mem_access_hazard_b: assert property (mem_access_hazard_b);

endmodule
