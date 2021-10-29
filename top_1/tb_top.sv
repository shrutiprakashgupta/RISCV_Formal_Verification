module tb_top (
input         clk_i,
input         reset_i,

//Interface signals - due to blackbox
input [31:0] irdata_i,
input [31:0] drdata_i,

input        ird_o,
input [31:0] iaddr_o,
input [31:0] daddr_o,
input [31:0] dwdata_o,
input  [1:0] dsize_o,
input  [3:0] dbe_w,
input        drd_o,
input        dwr_o,

//Interface signals - for observing signals
input [31:0] id_pc_r,
input [31:0] id_next_pc_r,
input        branch_taken_w,
input [31:0] jump_addr_w,
input        ex_stall_w
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
	
	//*****************************************Sanity check**************************************** 
	//Branch instruction 
   
	property branch;
		integer pc;
		@(posedge clk_i) disable iff (reset_i) 
			(!branch_taken_w && (irdata_i[14:12] == 3'b000) && (irdata_i[11:7] == 5'b10000) && (irdata_i[6:0] == 7'b1100011), pc = id_pc_r) 
		##1 ( branch_taken_w && (irdata_i[14:12] == 3'b111) && (irdata_i[6:0] == 7'b0110011) && (jump_addr_w == pc+36)) 
		##1 (!branch_taken_w && (irdata_i[14:12] == 3'b111) && (irdata_i[6:0] == 7'b0110011))[*20] 
		##1 1'b1;
	endproperty
	
	branch_instr: cover property (branch);
 
	//Division instruction introducing pipeline stall 
	property pipe_stall;
		@(posedge clk_i) disable iff (reset_i) 
			((irdata_i[6:0] == 7'b0110011) && (irdata_i[14:12] == 3'b100) && (irdata_i[31:25] == 7'b0000001)) 
			##1 (!branch_taken_w) && ((irdata_i[14:12] == 3'b000) && (irdata_i[6:0] == 7'b0010011)) 
			##37 1'b1;
	endproperty
	
	pipe_stall_div_instr: cover property (pipe_stall);
   
	//Back to back Division instructions introducing pipeline stall 
	property div_div;
		@(posedge clk_i) disable iff (reset_i) 
			((irdata_i[6:0] == 7'b0110011) && (irdata_i[14:12] == 3'b100) && (irdata_i[31:25] == 7'b0000001))
			##1 (!branch_taken_w) 
			##3 (!ex_stall_w) && ((irdata_i[14:12] == 3'b100) && (irdata_i[6:0] == 7'b0110011) && (irdata_i[31:25] == 7'b0000001)) 
			##37 1'b1;
	endproperty
	
	div_div_instr: cover property (div_div);

	//****************************************Testing Output - Assertions on Output*********************************
	//Word Alignment of Address
	property word_align;
		@(posedge clk_i) disable iff (reset_i) (id_pc_r[1:0] == 2'b0) 
											&& (id_next_pc_r[1:0] == 2'b0) 
	 										&& (iaddr_o[1:0] == 2'b00);
	endproperty
	
	prop_word_align: assert property (word_align);
	
	//-------------------------------------------------id_pc_r------------------------------------------------------
	//Assert: id_pc_r is a stored version of original PC so that it aligns with execute stage, which is one cycle delayed 
	property pc_delay;
		integer pc_stored;
		@(posedge clk_i) disable iff (reset_i) (1'b1, pc_stored = iaddr_o) |=> (id_pc_r == pc_stored);
	endproperty
	
	prop_pc_delay: assert property (pc_delay);
	
	//-----------------------------------------------id_next_pc_r---------------------------------------------------
	//id_next_pc_r value should be 4 ahead of pc_curr
	property next_pc_val;
		@(posedge clk_i) disable iff (reset_i) id_next_pc_r == (id_pc_r + 4);
	endproperty
	
	prop_next_pc_val: assert property (next_pc_val); 
	
	//-------------------------------------------------iaddr_o------------------------------------------------------
	//Assert: PC Increment in non-branch case
	property pc_inc;
		integer pc_curr;
		@(posedge clk_i) disable iff (reset_i) (!(branch_taken_w || ex_stall_w), pc_curr = iaddr_o) |=> iaddr_o == (pc_curr + 4);
	endproperty
	
	pc_inc_prop: assert property (pc_inc);
	
	//Assert: PC Value Change in branch case
	property pc_jump;
		integer jump_addr;
		@(posedge clk_i) disable iff (reset_i) (branch_taken_w, jump_addr = jump_addr_w[31:2]) |=> iaddr_o == {jump_addr, 2'b00};
	endproperty
	
	pc_jump_prop: assert property (pc_jump);

	//Assert: PC Value Stable while Stall is held high
	property pc_stall;
		@(posedge clk_i) disable iff (reset_i) (ex_stall_w && (!branch_taken_w)) |=> iaddr_o == $past(iaddr_o);
	endproperty
	
	pc_stall_prop: assert property (pc_stall);
endmodule
