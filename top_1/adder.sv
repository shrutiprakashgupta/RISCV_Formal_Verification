`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	adder
// Top module:  	top
// Linked modules: 	exe_stage
////////////////////////////////////////////////////////////////////////////////////////////

module adder(

input   [3:0] id_alu_op_r,
input  [31:0] id_ra_value_r,
input  [31:0] alu_opb_w,

output        adder_c_w,
output [31:0] adder_out_w,
output        adder_n_w,
output        adder_v_w,
output        adder_z_w
);

wire adder_sub_w = (`ALU_SUB == id_alu_op_r || `ALU_SLT == id_alu_op_r || `ALU_SLTU == id_alu_op_r);
wire [31:0] adder_opa_w = id_ra_value_r;
wire [31:0] adder_opb_w = adder_sub_w ? ~alu_opb_w : alu_opb_w;
wire        adder_cin_w = adder_sub_w ? 1'b1 : 1'b0;

assign adder_n_w = adder_out_w[31];
assign adder_v_w = (adder_opa_w[31] == adder_opb_w[31] && adder_out_w[31] != adder_opb_w[31]);
assign adder_z_w = (32'h0 == adder_out_w);
assign { adder_c_w, adder_out_w } = { 1'b0, adder_opa_w } + { 1'b0, adder_opb_w } + adder_cin_w;
    
endmodule
