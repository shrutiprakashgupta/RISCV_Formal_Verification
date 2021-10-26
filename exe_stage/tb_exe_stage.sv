`include "defines.sv"

module tb_exe_stage (

input        clk_i,
input        reset_i,

input  [3:0] id_alu_op_r,

input [31:0] id_ra_value_r,
input [31:0] id_rb_value_r,
input        id_a_signed_r,
input        id_b_signed_r,
input  [4:0] id_rd_index_r,

input [31:0] id_imm_r,
input        id_op_imm_r,

input [31:0] id_pc_reg,
input [31:0] id_next_pc_r,
input        id_reg_jump_r, 
input  [2:0] id_branch_r,

input        id_mem_rd_r,
input        id_mem_wr_r,
input  [1:0] id_mem_size_r,
input        id_mem_signed_r,

input        branch_taken_w,
input [31:0] jump_addr_w,

input  [4:0] ex_rd_index_r,
input [31:0] ex_alu_res_r,
input [31:0] ex_mem_data_r,
input        ex_mem_rd_r,
input        ex_mem_wr_r,
input        ex_mem_signed_r,
input  [1:0] ex_mem_size_r,

input        ex_stall_w
);
 
//-------------------------------------Restricting stimulus - Assumptions on Inputs------------------------------- 
	//Valid ALU Operation types
	property alu_op_types;
		@(posedge clk_i) disable iff (reset_i) (id_alu_op_r < 4'd15);
	endproperty
	
	prop_alu_op_types: assume property (alu_op_types); 

	//Signed nature of Operands valid for selected Operation types
	property val_signed_a;
		@(posedge clk_i) disable iff (reset_i) id_a_signed_r 
					|-> (id_alu_op_r inside {`ALU_MULH, `ALU_DIV, `ALU_REM, `ALU_SHR});
	endproperty
	
	prop_val_signed_a: assume property (val_signed_a);
	
	//Signed nature of Operands valid for selected Operation types
	property val_signed_b;
		@(posedge clk_i) disable iff (reset_i) id_b_signed_r 
					|-> (id_alu_op_r inside {`ALU_MULH, `ALU_DIV, `ALU_REM});
	endproperty
	
	prop_val_signed_b: assume property (val_signed_b); 
	
	//id_imm_r needs to be constrained as it can have no more than 12 original
	//bits and rest should be sign extended or zero padded 
	
	//Immediate Operands valid for selected Operation types
	property imm_opr;
		@(posedge clk_i) disable iff (reset_i) id_op_imm_r 
					|-> (!(id_alu_op_r inside {4'd9, 4'd10, 4'd11, 4'd12, 4'd1}) || id_mem_rd_r || id_mem_wr_r);
	endproperty
	
	prop_imm_opr: assume property (imm_opr); 
	
	//id_pc_r should freeze while the stall is high 
	property freeze_id_pc_reg;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_pc_reg == $past(id_pc_reg));
	endproperty
	
	prop_freeze_id_pc_reg: assume property (freeze_id_pc_reg);
	
	//id_pc_r should change to register value when jump is there
	//Here, the register value consists of both reg1 + offset or pc + offset
	//as per the jump instruction type 
	property jump_id_pc_reg;
		integer pc_target;
		@(posedge clk_i) disable iff (reset_i) (branch_taken_w, pc_target = jump_addr_w) |=> (id_pc_reg == {pc_target[31:2],2'b00});
	endproperty
	
	prop_jump_id_pc_reg: assume property (jump_id_pc_reg);
	
	//id_pc_r should increment by 4 in case no branch or stall 
	property inc_id_pc_reg;
		@(posedge clk_i) disable iff (reset_i) !(branch_taken_w || ex_stall_w) |=> (id_pc_reg == $past(id_pc_reg) + 32'h0000_0004);
	endproperty
	
	prop_inc_id_pc_reg: assume property (inc_id_pc_reg);
	//id_next_pc_r value should be 4 ahead of pc_curr
	property next_pc_val;
		@(posedge clk_i) disable iff (reset_i) id_next_pc_r == (id_pc_reg + 4);
	endproperty
	
	prop_next_pc_val: assume property (next_pc_val); 
	
	//id_reg_jump_r should be high only when the instruction was JALR i.e. ALU
	//instruction and branch at the same time 
	property reg_jump_instr;
		@(posedge clk_i) disable iff (reset_i) id_reg_jump_r 
					|-> (id_branch_r == 3'd1) && (id_alu_op_r == 4'd13);
	endproperty
	
	prop_reg_jump_instr: assume property (reg_jump_instr);
	
	//branch instruction is exclusive of the load and store
	//instructions 
	property branch_ex;
		@(posedge clk_i) disable iff (reset_i) (id_branch_r != 3'd0) 
					|-> (!id_mem_rd_r) && (!id_mem_wr_r) 
					&& (((id_branch_r == `BR_JUMP) && (id_alu_op_r == `ALU_NPC)) 
					|| ((id_branch_r != `BR_JUMP) && (id_alu_op_r == `ALU_SUB)));
	endproperty
	
	prop_branch_ex: assume property (branch_ex);
	
	//load store instructions are exclusive of the immediate and branch
	//instructions and are counted under ADD operations 
	property load_store_ex;
		@(posedge clk_i) disable iff (reset_i) (id_mem_rd_r || id_mem_wr_r) 
					|-> (!id_op_imm_r) && (id_branch_r == 3'd0) && (id_alu_op_r == `ALU_ADD);
	endproperty
	
	prop_load_store_ex: assume property (load_store_ex);
	
	//load store instructions are exclusive of each other 
	property load_or_store;
		@(posedge clk_i) disable iff (reset_i) !(id_mem_rd_r && id_mem_wr_r);
	endproperty
	
	prop_load_or_store: assume property (load_or_store);

	//inputs to the execute stage freeze while ex_stall_w remains high 
	property freeze_id_alu_op_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_alu_op_r == $past(id_alu_op_r));
	endproperty
	
	prop_freeze_id_alu_op_r: assume property (freeze_id_alu_op_r);

	property freeze_id_ra_value_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_ra_value_r == $past(id_ra_value_r));
	endproperty
	
	prop_freeze_id_ra_value_r: assume property (freeze_id_ra_value_r);

	property freeze_id_rb_value_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_rb_value_r == $past(id_rb_value_r));
	endproperty
	
	prop_freeze_id_rb_value_r: assume property (freeze_id_rb_value_r);

	property freeze_id_a_signed_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_a_signed_r == $past(id_a_signed_r));
	endproperty
	
	prop_freeze_id_a_signed_r: assume property (freeze_id_a_signed_r);

	property freeze_id_b_signed_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_b_signed_r == $past(id_b_signed_r));
	endproperty
	
	prop_freeze_id_b_signed_r: assume property (freeze_id_b_signed_r);

	property freeze_id_rd_index_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_rd_index_r == $past(id_rd_index_r));
	endproperty
	
	prop_freeze_id_rd_index_r: assume property (freeze_id_rd_index_r);

	property freeze_id_imm_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_imm_r == $past(id_imm_r));
	endproperty
	
	prop_freeze_id_imm_r: assume property (freeze_id_imm_r);

	property freeze_id_op_imm_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_op_imm_r == $past(id_op_imm_r));
	endproperty
	
	prop_freeze_id_op_imm_r: assume property (freeze_id_op_imm_r);

	//id_next_pc_r is used as execute stage data output in case of jump and link instruction, the value is verified to be always 
	//equal to PC + 4 in the next stage and so no explicit assertion here on
	//the id_next_pc_r signal 
	//id_next_pc_r is used as execute stage data output in case of jump and link instruction, the value is verified to be always 
	//equal to PC + 4 in the next stage and so no explicit assertion here on
	//the id_next_pc_r signal 
	//id_next_pc_r is used as execute stage data output in case of jump and link instruction, the value is verified to be always 
	//equal to PC + 4 in the next stage and so no explicit assertion here on
	//the id_next_pc_r signal 

	property freeze_id_next_pc_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_next_pc_r == $past(id_next_pc_r));
	endproperty
	
	prop_freeze_id_next_pc_r: assume property (freeze_id_next_pc_r);

	property freeze_id_reg_jump_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_reg_jump_r == $past(id_reg_jump_r));
	endproperty
	
	prop_freeze_id_reg_jump_r: assume property (freeze_id_reg_jump_r);

	property freeze_id_branch_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_branch_r == $past(id_branch_r));
	endproperty
	
	prop_freeze_id_branch_r: assume property (freeze_id_branch_r);

	property freeze_id_mem_rd_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_mem_rd_r == $past(id_mem_rd_r));
	endproperty
	
	prop_freeze_id_mem_rd_r: assume property (freeze_id_mem_rd_r);

	property freeze_id_mem_wr_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_mem_wr_r == $past(id_mem_wr_r));
	endproperty
	
	prop_freeze_id_mem_wr_r: assume property (freeze_id_mem_wr_r);
	property freeze_id_mem_size_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_mem_size_r == $past(id_mem_size_r));
	endproperty
	
	prop_freeze_id_mem_size_r: assume property (freeze_id_mem_size_r);

	property freeze_id_mem_signed_r;
		@(posedge clk_i) disable iff (reset_i) ex_stall_w |=> (id_mem_signed_r == $past(id_mem_signed_r));
	endproperty
	
	prop_freeze_id_mem_signed_r: assume property (freeze_id_mem_signed_r);

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
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_EQ) && (!taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_EQ, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_beq_fail: assert property (beq_fail);

   //Branch not taken unless A != B; with BNE 
   property bne_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_NE) && (!taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_NE, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bne_fail: assert property (bne_fail);

   //Branch not taken unless A < B; with BLT 
   property blt_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LT) && (!taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_LT, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_blt_fail: assert property (blt_fail);

   //Branch not taken unless A >= B; with BGE 
   property bge_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GE) && (!taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_GE, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bge_fail: assert property (bge_fail);

   //Branch not taken unless A < B unsigned comparison; with BLTU
   property bltu_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LTU) && (!taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_LTU, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bltu_fail: assert property (bltu_fail);

   //Branch not taken unless A >= B usigned comparison; with BGEU 
   property bgeu_fail;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GEU) && (!taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_GEU, branch_taken_w)) |=> !branch_taken_w;
   endproperty
  
   prop_bgeu_fail: assert property (bgeu_fail);


   //Branch taken if A = B; with BEQ 
   property beq_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_EQ) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_EQ, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_beq_pass: assert property (beq_pass);

   //Branch taken if A != B; with BNE 
   property bne_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_NE) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_NE, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_bne_pass: assert property (bne_pass);

   //Branch taken if A < B; with BLT 
   property blt_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LT) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_LT, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_blt_pass: assert property (blt_pass);

   //Branch taken if A >= B; with BGE 
   property bge_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GE) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_GE, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_bge_pass: assert property (bge_pass);

   //Branch taken if A < B unsigned comparison; with BLTU
   property bltu_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_LTU) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_LTU, branch_taken_w) |=> branch_taken_w;
   endproperty
  
   prop_bltu_pass: assert property (bltu_pass);

   //Branch taken if A >= B usigned comparison; with BGEU 
   property bgeu_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_GEU) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_GEU, branch_taken_w) |=> branch_taken_w;
   endproperty

   prop_bgeu_pass: assert property (bgeu_pass);

   //Branch taken whenever JUMP 
   property jump_pass;
      @(posedge clk_i) disable iff (reset_i) (id_branch_r == `BR_JUMP) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_JUMP, branch_taken_w) |=> branch_taken_w;
   endproperty

   prop_jump_pass: assert property (jump_pass);

   //Consecutive branch not allowed 
   property br_br_not_allowed;
      @(posedge clk_i) disable iff (reset_i) branch_taken_w |=> !branch_taken_w;
   endproperty

   prop_br_br_not_allowed: assert property (br_br_not_allowed);
   
   
   
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
      @(posedge clk_i) disable iff (reset_i) branch_taken_w && (id_rd_index_r != 0) && (id_branch_r == `BR_JUMP) && taken(id_ra_value_r, id_rb_value_r, id_imm_r, id_op_imm_r, `BR_JUMP, 1'b0)|=> (ex_rd_index_r == 0);
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
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_ADD) && (!branch_taken_w)), result_add = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_add);
   endproperty
  
   prop_add: assert property (add);

   //ALU_SUB
   property sub;
      integer result_sub; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SUB) && (!branch_taken_w)), result_sub = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_sub);
   endproperty
  
   prop_sub: assert property (sub);

   //ALU_AND
   property and_;
      integer result_and; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_AND) && (!branch_taken_w)), result_and = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_and);
   endproperty
  
   prop_and: assert property (and_);

   //ALU_OR
   property or_;
      integer result_or; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_OR) && (!branch_taken_w)), result_or = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_or);
   endproperty
  
   prop_or: assert property (or_);

   //ALU_XOR
   property xor_;
      integer result_xor; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_XOR) && (!branch_taken_w)), result_xor = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_xor);
   endproperty
  
   prop_xor: assert property (xor_);

   //ALU_SLT
   property slt;
      integer result_slt; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SLT) && (!branch_taken_w)), result_slt = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_slt);
   endproperty
  
   prop_slt: assert property (slt);

   //ALU_SLTU
   property sltu;
      integer result_sltu; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SLTU) && (!branch_taken_w)), result_sltu = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_sltu);
   endproperty
  
   prop_sltu: assert property (sltu);

   //ALU_SHL
   property shl;
      integer result_shl; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_SHL) && (!branch_taken_w)), result_shl = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_shl);
   endproperty
  
   prop_shl: assert property (shl);
   
   //ALU_MULL
   property mull;
      integer result_mull; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_MULL) && (!branch_taken_w)), result_mull = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_mull);
   endproperty
  
   prop_mull: assert property (mull);

   //ALU_MULH
   property mulh;
      integer result_mulh; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_MULH) && (!branch_taken_w)), result_mulh = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r)) |=> (ex_alu_res_r == result_mulh);
   endproperty
  
   prop_mulh: assert property (mulh);

   //ALU_DIV
   property div;
      integer result_div; 
      @(posedge clk_i) disable iff (reset_i) (((id_alu_op_r == `ALU_DIV) && (!branch_taken_w)), result_div = alu_out(id_ra_value_r, id_rb_value_r, id_a_signed_r, id_b_signed_r, id_imm_r, id_op_imm_r, id_alu_op_r, id_next_pc_r))  ##1 ex_stall_w [*1:31] ##1 (!ex_stall_w) |=> (ex_alu_res_r == result_div);
   endproperty
  
   prop_div: assert property (div);
  //-------------------------convergence for div => convergence for rem-----------------------------------
 
  //-----------------------------------------ex_mem_data_r------------------------------------------------
  //------------------------------------------ex_mem_wr_r-------------------------------------------------
  //------------------------------------------ex_mem_rd_r-------------------------------------------------
  //---------------------------------------ex_mem_signed_r------------------------------------------------
  //----------------------------------------ex_mem_size_r-------------------------------------------------
  //Direct assignment with input signal, no assertion needed
 
endmodule

