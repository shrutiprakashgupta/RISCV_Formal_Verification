`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	shifter
// Top module:  	top
// Linked modules: 	exe_stage
////////////////////////////////////////////////////////////////////////////////////////////

module shifter(
input         id_a_signed_r,
input  [31:0] id_ra_value_r,
input   [4:0] alu_opb_w,

output [31:0] sh_left_w,
output [31:0] sh_right_w
);

wire sh_fill_w = id_a_signed_r && id_ra_value_r[31];

wire [31:0] sl_0_w = alu_opb_w[0] ? { id_ra_value_r[30:0], 1'b0 } : id_ra_value_r;
wire [31:0] sl_1_w = alu_opb_w[1] ? { sl_0_w[29:0],  2'b0 } : sl_0_w;
wire [31:0] sl_2_w = alu_opb_w[2] ? { sl_1_w[27:0],  4'b0 } : sl_1_w;
wire [31:0] sl_3_w = alu_opb_w[3] ? { sl_2_w[23:0],  8'b0 } : sl_2_w;
wire [31:0] sl_4_w = alu_opb_w[4] ? { sl_3_w[15:0], 16'b0 } : sl_3_w;

wire [31:0] sr_0_w = alu_opb_w[0] ? {  {1{sh_fill_w}}, id_ra_value_r[31:1] } : id_ra_value_r;
wire [31:0] sr_1_w = alu_opb_w[1] ? {  {2{sh_fill_w}}, sr_0_w[31:2] }  : sr_0_w;
wire [31:0] sr_2_w = alu_opb_w[2] ? {  {4{sh_fill_w}}, sr_1_w[31:4] }  : sr_1_w;
wire [31:0] sr_3_w = alu_opb_w[3] ? {  {8{sh_fill_w}}, sr_2_w[31:8] }  : sr_2_w;
wire [31:0] sr_4_w = alu_opb_w[4] ? { {16{sh_fill_w}}, sr_3_w[31:16] } : sr_3_w;

assign sh_left_w  = sl_4_w;
assign sh_right_w = sr_4_w;

endmodule

