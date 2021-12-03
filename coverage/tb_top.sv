`include "defines.sv"

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

    //--------------------------------top_1-----------------------------------------------------------
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
	
    //---------------------------------top_2----------------------------------------------------------
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

    //------------------------------------top_3-------------------------------------------------------
//---------------------------------------Checking Behaviour-Assertions------------------------------------


   //-----------------------------------------branch_taken_w---------------------------------------------- 
   function integer taken (bit [31:0]a, bit [31:0]b, bit [31:0]imm_val, bit imm, bit [2:0]br_id, bit branch_taken_w);
      automatic bit [31:0] b_or_imm_val = imm ? imm_val : b;
      automatic bit branch;
      case(br_id)
         `BR_JUMP : branch = 1;
         `BR_EQ   : branch = (a == b_or_imm_val) ? 1 : 0;
         `BR_NE   : branch = (a != b_or_imm_val) ? 1 : 0;
         `BR_LT   : branch = ($signed(a) < $signed(b_or_imm_val)) ? 1 : 0;
         `BR_GE   : branch = ($signed(a) >= $signed(b_or_imm_val)) ? 1 : 0;
         `BR_LTU  : branch = (a < b_or_imm_val) ? 1 : 0;
         `BR_GEU  : branch = (a >= b_or_imm_val) ? 1 : 0;
         default  : branch = 0;
      endcase
      taken = branch_taken_w ? 0 : branch;
   endfunction 
   
   //Branch not taken unless A = B; with BEQ 
   property beq_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_EQ) && (!taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_EQ, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_beq_fail: assert property (beq_fail);

   //Branch not taken unless A != B; with BNE 
   property bne_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_NE) && (!taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_NE, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bne_fail: assert property (bne_fail);

   //Branch not taken unless A < B; with BLT 
   property blt_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LT) && (!taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_LT, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_blt_fail: assert property (blt_fail);

   //Branch not taken unless A >= B; with BGE 
   property bge_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GE) && (!taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_GE, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bge_fail: assert property (bge_fail);

   //Branch not taken unless A < B unsigned comparison; with BLTU
   property bltu_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LTU) && (!taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_LTU, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bltu_fail: assert property (bltu_fail);

   //Branch not taken unless A >= B usigned comparison; with BGEU 
   property bgeu_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GEU) && (!taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_GEU, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bgeu_fail: assert property (bgeu_fail);


   //Branch taken if A = B; with BEQ 
   property beq_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_EQ) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_EQ, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_beq_pass: assert property (beq_pass);

   //Branch taken if A != B; with BNE 
   property bne_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_NE) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_NE, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_bne_pass: assert property (bne_pass);

   //Branch taken if A < B; with BLT 
   property blt_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LT) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_LT, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_blt_pass: assert property (blt_pass);

   //Branch taken if A >= B; with BGE 
   property bge_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GE) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_GE, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_bge_pass: assert property (bge_pass);

   //Branch taken if A < B unsigned comparison; with BLTU
   property bltu_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LTU) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_LTU, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_bltu_pass: assert property (bltu_pass);

   //Branch taken if A >= B usigned comparison; with BGEU 
   property bgeu_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GEU) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_GEU, branch_taken_w) |=> branch_taken_w;
   endproperty

   prop_bgeu_pass: assert property (bgeu_pass);

   //Branch taken whenever JUMP 
   property jump_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_JUMP) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_JUMP, branch_taken_w) |=> branch_taken_w;
   endproperty

   prop_jump_pass: assert property (jump_pass);

   //Consecutive branch not allowed 
   property br_br_not_allowed;
      @(posedge clk_i) disable iff (reset_i) branch_taken_w |=> !branch_taken_w;
   endproperty

   prop_br_br_not_allowed: assert property (br_br_not_allowed);
   
    //--------------------------------------top_4--------------------------------------------------------   
   
   //--------------------------------------------jump_addr_w---------------------------------------------
   //this signal is direct assign statement which selects between the register
   //value and immediate operand to decide the branch target/destination, thus
   //no corresponding assertion needed 

   //-------------------------------------------ex_rd_index_r------------------------------------------
   //Dont know why but ex_rd_index_r is given value 2 out of reset 
   //Otherwise it is just signal forwarding, no need of assertion on it 
   //epoch is similar to branch_taken_w signal thus no need of separate
   //assertion for its validity
   //BR_JUMP
   property n_epoch_jump;
      @(posedge clk_i) disable iff (reset_i) branch_taken_w && (id_rd_index_r != 0) && (id_branch_r == `BR_JUMP) && taken(exe_ra_r, exe_rb_r, id_imm_r, id_op_imm_r, `BR_JUMP, 1'b0)|=> (ex_rd_index_r == 0);
   endproperty
  
   prop_n_epoch_jump: assert property (n_epoch_jump);
     

   //--------------------------------------------ex_alu_res_r--------------------------------------------
   //id_alu_op_r value will change - assertions for different values of this
   //signal 
   //
   //id_ra_value_r id_rb_value_r id_imm_r will be required, probably
   //id_a_signed_r id_b_signed_r will also be needed to decide the signdedness
   //of the output 
   //
   //id_op_imm_r and id_alu_op_r will be needed - in assertion and in function
   //both
   //
   //id_next_pc_r will be needed in function 
   //
   //id_branch_r should be 0 and id_mem_rd_r and id_mem_wr_r both should be 0
   function int unsigned alu_out (int ra, int rb, bit a_signed, bit b_signed, int imm_val, bit imm, bit [3:0] alu_op, int next_pc);
      automatic int              b_or_imm_val = imm ? imm_val : rb;
      automatic int     unsigned a_32         = a_signed && ra[31] ? (~ra + 32'b0000_0001) : ra; 
      automatic int     unsigned b_32         = b_signed && b_or_imm_val[31] ? (~b_or_imm_val + 32'b0000_0001) : b_or_imm_val; 
	  automatic int		unsigned a_div		  = a_32 / b_32;
      automatic longint unsigned a_64         = a_signed ? {{32{ra[31]}},ra} : ra; 
      automatic longint unsigned b_64         = b_signed ? {{32{b_or_imm_val[31]}},b_or_imm_val} : b_or_imm_val;
      automatic longint unsigned mul          = a_64 * b_64; 
      case(alu_op)
         `ALU_ADD   : alu_out = ra + b_or_imm_val; 
         `ALU_SUB   : alu_out = ra - b_or_imm_val;
         `ALU_AND   : alu_out = ra & b_or_imm_val;
         `ALU_OR    : alu_out = ra | b_or_imm_val;
         `ALU_XOR   : alu_out = ra ^ b_or_imm_val;
         `ALU_SLT   : alu_out = $signed(ra) < $signed(b_or_imm_val);
         `ALU_SLTU  : alu_out = $unsigned(ra) < $unsigned(b_or_imm_val);
         `ALU_SHL   : alu_out = ra << b_or_imm_val[4:0];
         `ALU_SHR   : alu_out = a_signed ? $signed(ra) >>> b_or_imm_val[4:0] : $signed(ra) >> b_or_imm_val[4:0];
         `ALU_MULL  : alu_out = mul;
         `ALU_MULH  : alu_out = mul >> 32;
         `ALU_DIV   : alu_out = ((a_signed && ra[31]) ^ (b_signed && b_or_imm_val[31])) ? (~a_div + 1'b1) : a_div;
         `ALU_REM   : alu_out = 0;
         `ALU_NPC   : alu_out = next_pc; //Direct assign statement 
         `ALU_AUIPC : alu_out = 0; //Direct assign statement  
         default    : alu_out = 0;
      endcase
      return alu_out;
   endfunction 
   
   //ALU_ADD
   property add;
      integer result_add; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_ADD) && (!branch_taken_w)), result_add = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_add);
   endproperty
  
   prop_add: assert property (add);

   //ALU_SUB
   property sub;
      integer result_sub; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SUB) && (!branch_taken_w)), result_sub = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_sub);
   endproperty
  
   prop_sub: assert property (sub);

   //ALU_AND
   property and_;
      integer result_and; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_AND) && (!branch_taken_w)), result_and = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_and);
   endproperty
  
   prop_and: assert property (and_);

   //ALU_OR
   property or_;
      integer result_or; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_OR) && (!branch_taken_w)), result_or = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_or);
   endproperty
  
   prop_or: assert property (or_);

   //ALU_XOR
   property xor_;
      integer result_xor; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_XOR) && (!branch_taken_w)), result_xor = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_xor);
   endproperty
  
   prop_xor: assert property (xor_);

   //ALU_SLT
   property slt;
      integer result_slt; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SLT) && (!branch_taken_w)), result_slt = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_slt);
   endproperty
  
   prop_slt: assert property (slt);

   //ALU_SLTU
   property sltu;
      integer result_sltu; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SLTU) && (!branch_taken_w)), result_sltu = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_sltu);
   endproperty
  
   prop_sltu: assert property (sltu);

   //ALU_SHL
   property shl;
      integer result_shl; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SHL) && (!branch_taken_w)), result_shl = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_shl);
   endproperty
  
   prop_shl: assert property (shl);
   
   //ALU_MULL
   property mull;
      integer result_mull; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_MULL) && (!branch_taken_w)), result_mull = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_mull);
   endproperty
  
   prop_mull: assert property (mull);

   //ALU_MULH
   property mulh;
      integer result_mulh; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_MULH) && (!branch_taken_w)), result_mulh = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_mulh);
   endproperty
  
   prop_mulh: assert property (mulh);

   //ALU_DIV
   property div;
      integer result_div; 
      @(posedge clk_i) disable iff (reset_i) (!ex_stall_w) ##1 (((id_alu_op_r == `ALU_DIV) && (!branch_taken_w) && ex_stall_w), result_div = alu_out(exe_ra_r, exe_rb_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r))  ##1 ex_stall_w [*32] ##1 (!ex_stall_w) |=> (ex_alu_res_r == result_div);
   endproperty
  
   prop_div: assert property (div);
  //-------------------------convergence for div => convergence for rem-----------------------------------
 
  //-----------------------------------------ex_mem_data_r------------------------------------------------
  //------------------------------------------ex_mem_wr_r-------------------------------------------------
  //------------------------------------------ex_mem_rd_r-------------------------------------------------
  //---------------------------------------ex_mem_signed_r------------------------------------------------
  //----------------------------------------ex_mem_size_r-------------------------------------------------
  //Direct assignment with input signal, no assertion needed

	//Testing Output - Assertions on Output
	//--------------------------------------------daddr_o---------------------------------------------
	//Directly assigned the input coming from the execute stage, thus memory
	//alignement not guarenteed. This can be prevented from causing an issue in
	//the memory block itself - Thus no explicit assertion 
	
	//--------------------------------------------dwdata_o--------------------------------------------
	//Data passed directly, this would require byte-writability in memory  
	
	//-----------------------------------------mem_rdata_for_hazard-----------------------------------
	//--------------------------------------------mem_rdata_w-----------------------------------------
	//Check sign extension or zero padding based on the read flag status, and
	//the data size
	
	//Signed byte read
	property signed_byte_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_BYTE) & (ex_mem_rd_r) & (ex_mem_signed_r) |=> (mem_rdata_w[31:8] == {24{mem_rdata_w[7]}}); 
	endproperty
	
	prop_signed_byte_read: assert property (signed_byte_read);
	
	//Unsigned byte read
	property unsigned_byte_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_BYTE) & (ex_mem_rd_r) & (!ex_mem_signed_r) |=> (mem_rdata_w[31:8] == 24'b0); 
	endproperty
	
	prop_unsigned_byte_read: assert property (unsigned_byte_read);
	
	//Signed hlaf read
	property signed_half_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_HALF) & (ex_mem_rd_r) & (ex_mem_signed_r) |=> (mem_rdata_w[31:16] == {16{mem_rdata_w[15]}}); 
	endproperty
	
	prop_signed_half_read: assert property (signed_half_read);
	
	//Unsigned half read
	property unsigned_half_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_HALF) & (ex_mem_rd_r) & (!ex_mem_signed_r) |=> (mem_rdata_w[31:16] == 16'h0); 
	endproperty
	
	prop_unsigned_half_read: assert property (unsigned_half_read);

endmodule
