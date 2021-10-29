`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	exe_stage
// Top module:  	top
// Linked modules: 	stage1, hazard_detection, mem_stage, adder, shifter, multiplier, divider
////////////////////////////////////////////////////////////////////////////////////////////
`include "defines.sv"        
     
module exe_stage(

input             clk_i,
input             reset_i,

input       [3:0] id_alu_op_r,

input      [31:0] id_ra_value_r,
input      [31:0] id_rb_value_r,
input             id_a_signed_r,
input             id_b_signed_r,
input       [4:0] id_rd_index_r,

input      [31:0] id_imm_r,
input             id_op_imm_r,

input      [31:0] id_pc_reg,
input      [31:0] id_next_pc_r,
input             id_reg_jump_r, 
input       [2:0] id_branch_r,

input             id_mem_rd_r,
input             id_mem_wr_r,
input       [1:0] id_mem_size_r,
input             id_mem_signed_r, 

output reg        branch_taken_w,
output reg [31:0] jump_addr_w,

output reg  [4:0] ex_rd_index_r,
output reg [31:0] ex_alu_res_r,
output reg [31:0] ex_mem_data_r,
output reg        ex_mem_rd_r,
output reg        ex_mem_wr_r,
output reg        ex_mem_signed_r,
output reg  [1:0] ex_mem_size_r,

output            ex_stall_w
);

reg [31:0] ex_alu_res_w_internal;
reg epoch;
reg b_w;
reg [31:0] jump_addr_r;

wire [31:0] alu_opb_w = id_op_imm_r ? id_imm_r : id_rb_value_r;

wire adder_c_w;
wire [31:0] adder_out_w;
wire adder_n_w;
wire adder_v_w;
wire adder_z_w;

wire [31:0] sh_left_w;
wire [31:0] sh_right_w;

wire mul_div_negative_w = (id_a_signed_r && id_ra_value_r[31]) ^ (id_b_signed_r && id_rb_value_r[31]);
wire [31:0] mul_div_a_w = (id_a_signed_r && id_ra_value_r[31]) ? -id_ra_value_r : id_ra_value_r;
wire [31:0] mul_div_b_w = (id_b_signed_r && id_rb_value_r[31]) ? -id_rb_value_r : id_rb_value_r;

wire [63:0] mul_res_w;
wire ex_stall_mul_w;

wire [31:0] div_quotient_w;
wire [31:0] div_remainder_w;
wire ex_stall_div_w;

wire exe_bubble_w = b_w && epoch;

assign ex_stall_w = ex_stall_div_w;

adder adder_from_alu(
    .id_alu_op_r(id_alu_op_r),
    .id_ra_value_r(id_ra_value_r),
    .alu_opb_w(alu_opb_w),
     //output
    .adder_c_w(adder_c_w),
    .adder_out_w(adder_out_w),
    .adder_n_w(adder_n_w),
    .adder_v_w(adder_v_w),
    .adder_z_w(adder_z_w)
);
   
shifter shifter_from_alu(
    .id_a_signed_r(id_a_signed_r),
    .id_ra_value_r(id_ra_value_r),
    .alu_opb_w(alu_opb_w[4:0]),
     //output
    .sh_left_w(sh_left_w),
    .sh_right_w(sh_right_w)
);

multiplier multiplier_from_alu(
    .id_ra_value_r(id_ra_value_r),
    .id_rb_value_r(id_rb_value_r),
    .id_a_signed_r(id_a_signed_r),
    .id_b_signed_r(id_b_signed_r),
     //output
    .mul_res_w(mul_res_w)
);

divider divider_from_alu(
    .clk_i(clk_i),
    .reset_i(reset_i || branch_taken_w),
    .id_alu_op_r(id_alu_op_r),
    .mul_div_negative_w(mul_div_negative_w),
    .mul_div_a_w(mul_div_a_w),
    .mul_div_b_w(mul_div_b_w),
     //output
    .div_quotient_w(div_quotient_w),
    .div_remainder_w(div_remainder_w),
    .ex_stall_div_w(ex_stall_div_w)
);
    
always @(*) begin

b_w = (`BR_JUMP == id_branch_r) ? 1'b1 :
      (`BR_EQ   == id_branch_r) ? adder_z_w :
      (`BR_NE   == id_branch_r) ? !adder_z_w :
      (`BR_LT   == id_branch_r) ? adder_n_w != adder_v_w :
      (`BR_GE   == id_branch_r) ? adder_n_w == adder_v_w :
      (`BR_LTU  == id_branch_r) ? !adder_c_w :
      (`BR_GEU  == id_branch_r) ? adder_c_w : 1'b0; 

jump_addr_r = (id_reg_jump_r ? id_ra_value_r : id_pc_reg) + id_imm_r;

case (id_alu_op_r)
    `ALU_ADD   : ex_alu_res_w_internal = adder_out_w;
    `ALU_SUB   : ex_alu_res_w_internal = adder_out_w;
    `ALU_AND   : ex_alu_res_w_internal = id_ra_value_r & alu_opb_w;
    `ALU_OR    : ex_alu_res_w_internal = id_ra_value_r | alu_opb_w;
    `ALU_XOR   : ex_alu_res_w_internal = id_ra_value_r ^ alu_opb_w;
    `ALU_SLT   : ex_alu_res_w_internal = (adder_n_w != adder_v_w) ? 32'h1 : 32'h0;
    `ALU_SLTU  : ex_alu_res_w_internal = (adder_c_w == 1'b0) ? 32'h1 : 32'h0;
    `ALU_SHL   : ex_alu_res_w_internal = sh_left_w;
    `ALU_SHR   : ex_alu_res_w_internal = sh_right_w;
    `ALU_MULL  : ex_alu_res_w_internal = mul_res_w[31:0];
    `ALU_MULH  : ex_alu_res_w_internal = mul_res_w[63:32];
    `ALU_DIV   : ex_alu_res_w_internal = div_quotient_w;
    `ALU_REM   : ex_alu_res_w_internal = div_remainder_w;
    `ALU_NPC   : ex_alu_res_w_internal = id_next_pc_r;
    `ALU_AUIPC : ex_alu_res_w_internal = jump_addr_r;
    default   : ex_alu_res_w_internal = 32'h0;
endcase
end
   
always @(posedge clk_i or posedge reset_i) begin
   if(reset_i) begin
      epoch<=1;
   end else if(exe_bubble_w) begin
      epoch<=0;
   end else begin
      epoch<=1;
   end
end
     
always @(posedge clk_i or posedge reset_i) begin
       if (reset_i) begin
            ex_rd_index_r   <= 5'd2; // SP
            ex_alu_res_r    <= `RESET_SP;
            ex_mem_data_r   <= 32'h0;
            ex_mem_rd_r     <= 1'b0;
            ex_mem_wr_r     <= 1'b0;
            ex_mem_signed_r <= 1'b0;
            ex_mem_size_r   <= `SIZE_BYTE;
            branch_taken_w  <= 0;
            jump_addr_w     <= 0;
        end
        else if(~epoch) begin
            ex_rd_index_r   <= 5'd0; // SP
            ex_alu_res_r    <= 0;
            ex_mem_data_r   <= 32'h0;
            ex_mem_rd_r     <= 1'b0;
            ex_mem_wr_r     <= 1'b0;
            ex_mem_signed_r <= 1'b0;
            ex_mem_size_r   <= `SIZE_BYTE;
            branch_taken_w  <= 0;
            jump_addr_w     <= 0;
            end
       else begin
            ex_rd_index_r   <= id_rd_index_r;
            ex_alu_res_r    <= ex_alu_res_w_internal;
            ex_mem_data_r   <= id_rb_value_r;
            ex_mem_rd_r     <= id_mem_rd_r;
            ex_mem_wr_r     <= id_mem_wr_r;
            ex_mem_signed_r <= id_mem_signed_r;
            ex_mem_size_r   <= id_mem_size_r;
            jump_addr_w     <= jump_addr_r;
            branch_taken_w  <= b_w;
        end
    end
   
endmodule

