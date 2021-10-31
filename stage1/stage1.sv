`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	stage1
// Top module:  	top
// Linked modules: 	exe_stage, hazard_detection,
/////////////////////////////////////////////////////////////////////////////////////////////
`include "defines.sv"

module stage1 (
input             clk_i,
input             reset_i,
input      [31:0] irdata_i,
input             branch_taken_w,
input      [31:0] jump_addr_w,
input             ex_stall_w,

output reg [31:0] id_pc_r,
output reg [31:0] id_next_pc_r,
output reg  [4:0] id_rd_index_r,
output reg  [4:0] addr_1,
output reg  [4:0] addr_2,
output reg        id_a_signed_r,
output reg        id_b_signed_r,
output reg  [3:0] id_alu_op_r,

output reg [31:0] id_imm_r,
output reg        id_op_imm_r,

output reg        id_mem_rd_r,
output reg        id_mem_wr_r,
output reg        id_mem_signed_r,
output reg  [1:0] id_mem_size_r,

output reg  [2:0] id_branch_r,
output reg        id_reg_jump_r,

output reg [31:0] iaddr_o,
output reg        ird_o

);

typedef struct packed  {

	bit [4:0] id_rd_index_w;
	bit [4:0] id_ra_index_w;
	bit [4:0] id_rb_index_w;
	bit mulh_w,mulhsu_w,div_w;
	bit rem_w;
	bit lbu_w,lhu_w;
	bit sra_w;
	bit srai_w;
	bit load_w,store_w,alu_imm_w,id_illegal_w;
	bit jal_w,jalr_w;
	bit [3:0] id_alu_op_w;
	bit [2:0] id_branch_w;
	bit [1:0] id_mem_size_w;
	bit [31:0] id_imm_w;

} decode_struct;

wire [31:0] if_opcode ;

function decode_struct decode_combo_logic(input [31:0] if_opcode_w) ;

bit [6:0] op_w;
bit [4:0] rd_w ;
bit [2:0] f3_w ;
bit [4:0] ra_w;
bit [4:0] rb_w ;
bit [6:0] f7_w ;

bit op_branch_w,op_load_w,op_store_w,op_alu_imm_w,op_alu_reg_w;
bit op_f7_main_w,op_f7_alt_w,op_f7_mul_w;
bit lui_w,auipc_w;
bit jal_w,jalr_w,beq_w,bne_w,blt_w,bltu_w,bgeu_w,bge_w;
bit lb_w,lh_w,lw_w,lbu_w,lhu_w;
bit sb_w,sh_w,sw_w;
bit addi_w,slti_w,sltiu_w,xori_w,ori_w,andi_w,slli_w,srli_w,srai_w;
bit add_w,sub_w,slt_w,sltu_w,xor_w,or_w,and_w,sll_w,srl_w,sra_w;
bit mul_w,mulh_w,mulhsu_w,mulhu_w,div_w,divu_w,rem_w,remu_w;
bit load_w,store_w,alu_imm_w,alu_reg_w,branch_w,jump_w,id_illegal_w;

bit [31:0] id_i_imm_w,id_s_imm_w,id_b_imm_w,id_u_imm_w,id_j_imm_w,id_imm_w;
bit [4:0] id_rd_index_w,id_ra_index_w,id_rb_index_w;
bit [3:0] id_alu_op_w;
bit [2:0] id_branch_w;
bit [1:0] id_mem_size_w;

decode_struct d1;

op_w = if_opcode_w[6:0];
rd_w = if_opcode_w[11:7];
f3_w = if_opcode_w[14:12];
ra_w = if_opcode_w[19:15];
rb_w = if_opcode_w[24:20];
f7_w = if_opcode_w[31:25];

op_branch_w  = (7'b1100011 == op_w);
op_load_w    = (7'b0000011 == op_w);
op_store_w   = (7'b0100011 == op_w);
op_alu_imm_w = (7'b0010011 == op_w);
op_alu_reg_w = (7'b0110011 == op_w);

op_f7_main_w = (7'b0000000 == f7_w);
op_f7_alt_w  = (7'b0100000 == f7_w);
op_f7_mul_w  = (7'b0000001 == f7_w);

lui_w    = (7'b0110111 == op_w);
auipc_w  = (7'b0010111 == op_w);
jal_w    = (7'b1101111 == op_w);
jalr_w   = (7'b1100111 == op_w) && (3'b000 == f3_w);

beq_w    = op_branch_w  && (3'b000 == f3_w);
bne_w    = op_branch_w  && (3'b001 == f3_w);
blt_w    = op_branch_w  && (3'b100 == f3_w);
bge_w    = op_branch_w  && (3'b101 == f3_w);
bltu_w   = op_branch_w  && (3'b110 == f3_w);
bgeu_w   = op_branch_w  && (3'b111 == f3_w);

lb_w     = op_load_w    && (3'b000 == f3_w);
lh_w     = op_load_w    && (3'b001 == f3_w);
lw_w     = op_load_w    && (3'b010 == f3_w);
lbu_w    = op_load_w    && (3'b100 == f3_w);
lhu_w    = op_load_w    && (3'b101 == f3_w);

sb_w     = op_store_w   && (3'b000 == f3_w);
sh_w     = op_store_w   && (3'b001 == f3_w);
sw_w     = op_store_w   && (3'b010 == f3_w);

addi_w   = op_alu_imm_w && (3'b000 == f3_w);
slti_w   = op_alu_imm_w && (3'b010 == f3_w);
sltiu_w  = op_alu_imm_w && (3'b011 == f3_w);
xori_w   = op_alu_imm_w && (3'b100 == f3_w);
ori_w    = op_alu_imm_w && (3'b110 == f3_w);
andi_w   = op_alu_imm_w && (3'b111 == f3_w);
slli_w   = op_alu_imm_w && (3'b001 == f3_w) && op_f7_main_w;
srli_w   = op_alu_imm_w && (3'b101 == f3_w) && op_f7_main_w;
srai_w   = op_alu_imm_w && (3'b101 == f3_w) && op_f7_alt_w;

add_w    = op_alu_reg_w && (3'b000 == f3_w) && op_f7_main_w;
sub_w    = op_alu_reg_w && (3'b000 == f3_w) && op_f7_alt_w;
slt_w    = op_alu_reg_w && (3'b010 == f3_w) && op_f7_main_w;
sltu_w   = op_alu_reg_w && (3'b011 == f3_w) && op_f7_main_w;
xor_w    = op_alu_reg_w && (3'b100 == f3_w) && op_f7_main_w;
or_w     = op_alu_reg_w && (3'b110 == f3_w) && op_f7_main_w;
and_w    = op_alu_reg_w && (3'b111 == f3_w) && op_f7_main_w;
sll_w    = op_alu_reg_w && (3'b001 == f3_w) && op_f7_main_w;
srl_w    = op_alu_reg_w && (3'b101 == f3_w) && op_f7_main_w;
sra_w    = op_alu_reg_w && (3'b101 == f3_w) && op_f7_alt_w;
mul_w    = op_alu_reg_w && (3'b000 == f3_w) && op_f7_mul_w;
mulh_w   = op_alu_reg_w && (3'b001 == f3_w) && op_f7_mul_w;
mulhsu_w = op_alu_reg_w && (3'b010 == f3_w) && op_f7_mul_w;
mulhu_w  = op_alu_reg_w && (3'b011 == f3_w) && op_f7_mul_w;
div_w    = op_alu_reg_w && (3'b100 == f3_w) && op_f7_mul_w;
divu_w   = op_alu_reg_w && (3'b101 == f3_w) && op_f7_mul_w;
rem_w    = op_alu_reg_w && (3'b110 == f3_w) && op_f7_mul_w;
remu_w   = op_alu_reg_w && (3'b111 == f3_w) && op_f7_mul_w;


load_w    = lb_w || lh_w || lw_w || lbu_w || lhu_w;
store_w   = sb_w || sh_w || sw_w;
alu_imm_w = addi_w || slti_w || sltiu_w || xori_w || ori_w || andi_w ||
                slli_w || srli_w || srai_w || lui_w || auipc_w;
alu_reg_w = add_w || sub_w || slt_w || sltu_w || xor_w || or_w || and_w ||
                sll_w || srl_w || sra_w || mul_w || mulh_w || mulhsu_w ||
                mulhu_w || div_w || divu_w || rem_w || remu_w;
branch_w  = beq_w || bne_w || blt_w || bge_w || bltu_w || bgeu_w;
jump_w    = jal_w || jalr_w;
id_illegal_w = !(load_w || store_w || alu_imm_w || alu_reg_w || jump_w || branch_w);
id_i_imm_w = { {20{if_opcode_w[31]}}, if_opcode_w[31:20] };
id_s_imm_w = { {20{if_opcode_w[31]}}, if_opcode_w[31:25], if_opcode_w[11:7] };
id_b_imm_w = { {19{if_opcode_w[31]}}, if_opcode_w[31], if_opcode_w[7], if_opcode_w[30:25], if_opcode_w[11:8], 1'b0 };

id_u_imm_w = { if_opcode_w[31:12], 12'h0 };
id_j_imm_w = { {11{if_opcode_w[31]}}, if_opcode_w[31], if_opcode_w[19:12], if_opcode_w[20], if_opcode_w[30:21], 1'b0 };

id_imm_w =
	(lui_w || auipc_w)              ? id_u_imm_w :
	(branch_w)                      ? id_b_imm_w :
	(load_w || jalr_w || alu_imm_w) ? id_i_imm_w :
	(store_w)                       ? id_s_imm_w :
	(jal_w)                         ? id_j_imm_w : 32'h0;

id_rd_index_w = (branch_w || store_w)           ? 5'd0 : rd_w;
id_ra_index_w = (lui_w || auipc_w || jal_w)     ? 5'd0 : ra_w;
id_rb_index_w = (load_w || jump_w || alu_imm_w) ? 5'd0 : rb_w;

id_alu_op_w =
	(add_w || addi_w || lui_w || load_w || store_w) ? `ALU_ADD :
	(andi_w || and_w)                    ? `ALU_AND :
	(ori_w || or_w)                      ? `ALU_OR :
	(xori_w || xor_w)                    ? `ALU_XOR :
	(slti_w || slt_w)                    ? `ALU_SLT :
	(sltiu_w || sltu_w)                  ? `ALU_SLTU :
	(sll_w || slli_w)                    ? `ALU_SHL :
	(srl_w || srli_w || sra_w || srai_w) ? `ALU_SHR :
	(mulh_w || mulhsu_w || mulhu_w)      ? `ALU_MULH :
	(mul_w)                              ? `ALU_MULL :
	(div_w || divu_w)                    ? `ALU_DIV :
	(rem_w || remu_w)                    ? `ALU_REM :
	(jal_w || jalr_w)                    ? `ALU_NPC :
	(auipc_w)                            ? `ALU_AUIPC : `ALU_SUB;

id_branch_w =
	beq_w  ? `BR_EQ :
	bne_w  ? `BR_NE :
	blt_w  ? `BR_LT :
	bge_w  ? `BR_GE :
	bltu_w ? `BR_LTU :
	bgeu_w ? `BR_GEU :
	jump_w ? `BR_JUMP : `BR_NONE;

id_mem_size_w =
	(lb_w || lbu_w || sb_w) ? `SIZE_BYTE :
	(lh_w || lhu_w || sh_w) ? `SIZE_HALF : `SIZE_WORD;

d1.lbu_w         = lbu_w;
d1.lhu_w         = lhu_w;
d1.mulh_w        = mulh_w;
d1.mulhsu_w      = mulhsu_w;
d1.div_w         = div_w;
d1.rem_w         = rem_w;
d1.sra_w         = sra_w;
d1.srai_w        = srai_w;
d1.jal_w         = jal_w;
d1.jalr_w        = jalr_w;
d1.load_w        = load_w;
d1.store_w       = store_w;
d1.alu_imm_w     = alu_imm_w;
d1.id_illegal_w  = id_illegal_w;
d1.id_alu_op_w   = id_alu_op_w;
d1.id_branch_w   = id_branch_w;
d1.id_mem_size_w = id_mem_size_w;
d1.id_imm_w      = id_imm_w;
d1.id_rd_index_w = id_rd_index_w;
d1.id_ra_index_w = id_ra_index_w;
d1.id_rb_index_w = id_rb_index_w;
return  d1 ;

endfunction

decode_struct d2;

reg  [31:0] if_pc_r;
reg  [31:2] if_addr_r;
reg         div_instr;
wire [31:0] if_next_pc_w   = if_pc_r + 4;
wire [31:2] if_next_addr_w = reset_i ? 0
							: branch_taken_w ? jump_addr_w[31:2]
							: (div_instr || ex_stall_w) ? if_addr_r
							: if_addr_r + 30'h0000_0001;

always@(posedge clk_i or posedge reset_i) begin
	if (reset_i) begin
		if_addr_r <= 'h0;
	end else begin
		if_addr_r <= if_next_addr_w;
	end
end

always @(posedge clk_i or posedge reset_i) begin
	if (reset_i) begin
		if_pc_r <= 32'h0;
	end else begin
		if_pc_r <= (if_next_addr_w<<2);
	end
end

assign d2 = decode_combo_logic(irdata_i);

always @(posedge clk_i or posedge reset_i) begin
	if (reset_i) begin
		div_instr <= 0;
	end else begin
		if(div_instr == 1) begin
			div_instr <= 0;
		end
		else begin
			if((!branch_taken_w) && (d2.id_alu_op_w == `ALU_DIV) && (!ex_stall_w)) begin
				div_instr <= 1;
			end
		end
	end
end

always @(posedge clk_i or posedge reset_i) begin

	if (reset_i) begin
		id_pc_r         <= 4;
		id_next_pc_r    <= 8;
		id_rd_index_r   <= 5'd0;
		id_imm_r        <= 32'h0;
		id_a_signed_r   <= 1'b0;
		id_b_signed_r   <= 1'b0;
		id_op_imm_r     <= 1'b0;
		id_alu_op_r     <= `ALU_ADD;
		id_mem_rd_r     <= 1'b0;
		id_mem_wr_r     <= 1'b0;
		id_mem_signed_r <= 1'b0;
		id_mem_size_r   <= `SIZE_BYTE;
		id_branch_r     <= `BR_NONE;
		id_reg_jump_r   <= 1'b0;
		addr_1          <= 0;
		addr_2          <= 0;
		iaddr_o         <= 0;
		ird_o           <= 0;
	end
	else if (branch_taken_w) begin
		id_pc_r         <= if_pc_r;
		id_next_pc_r    <= if_next_pc_w;
		id_rd_index_r   <= 5'd0;
		id_imm_r        <= 32'h0;
		id_a_signed_r   <= 1'b0;
		id_b_signed_r   <= 1'b0;
		id_op_imm_r     <= 1'b0;
		id_alu_op_r     <= `ALU_ADD;
		id_mem_rd_r     <= 1'b0;
		id_mem_wr_r     <= 1'b0;
		id_mem_signed_r <= 1'b0;
		id_mem_size_r   <= `SIZE_BYTE;
		id_branch_r     <= `BR_NONE;
		id_reg_jump_r   <= 1'b0;
		addr_1          <= 0;
		addr_2          <= 0;
		iaddr_o         <= if_next_addr_w<<2;
		ird_o           <= 1;
	end
	else if(div_instr || ex_stall_w) begin
		id_pc_r         <= if_pc_r;
		id_next_pc_r    <= if_next_pc_w;
		id_rd_index_r   <= id_rd_index_r;
		id_imm_r        <= id_imm_r;
		id_a_signed_r   <= id_a_signed_r;
		id_b_signed_r   <= id_b_signed_r;
		id_op_imm_r     <= id_op_imm_r;
		id_alu_op_r     <= id_alu_op_r;
		id_mem_rd_r     <= id_mem_rd_r;
		id_mem_wr_r     <= id_mem_wr_r;
		id_mem_signed_r <= id_mem_signed_r;
		id_mem_size_r   <= id_mem_size_r;
		id_branch_r     <= id_branch_r;
		id_reg_jump_r   <= id_reg_jump_r;
		addr_1          <= addr_1;
		addr_2          <= addr_2;
		iaddr_o         <= if_next_addr_w<<2;
		ird_o           <= 1;
	end
	else begin
		id_pc_r         <= if_pc_r;
		id_next_pc_r    <= if_next_pc_w;
		id_rd_index_r   <= d2.id_rd_index_w;
		id_imm_r        <= d2.id_imm_w;
		id_a_signed_r   <= d2.mulh_w || d2.mulhsu_w || d2.div_w || d2.rem_w || d2.sra_w || d2.srai_w;
		id_b_signed_r   <= d2.mulh_w || d2.div_w || d2.rem_w;
		id_op_imm_r     <= d2.alu_imm_w || d2.jal_w || d2.load_w || d2.store_w;
		id_alu_op_r     <= d2.id_alu_op_w;
		id_mem_rd_r     <= d2.load_w;
		id_mem_wr_r     <= d2.store_w;
		id_mem_signed_r <= !d2.lbu_w && !d2.lhu_w;
		id_mem_size_r   <= d2.id_mem_size_w;
		id_branch_r     <= d2.id_branch_w;
		id_reg_jump_r   <= d2.jalr_w;
		addr_1          <= d2.id_ra_index_w;
		addr_2          <= d2.id_rb_index_w;
		iaddr_o         <= if_next_addr_w<<2;
		ird_o           <= 1;
	end
end

endmodule
