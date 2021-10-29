`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	multiplier
// Top module:  	top
// Linked modules: 	exe_stage
////////////////////////////////////////////////////////////////////////////////////////////

module multiplier(

input  [31:0] id_ra_value_r,
input  [31:0] id_rb_value_r,
input         id_a_signed_r,
input         id_b_signed_r,

output [63:0] mul_res_w
);
    
wire mul_div_negative_w = (id_a_signed_r && id_ra_value_r[31]) ^ (id_b_signed_r && id_rb_value_r[31]);
wire [31:0] mul_div_a_w = (id_a_signed_r && id_ra_value_r[31]) ? -id_ra_value_r : id_ra_value_r;
wire [31:0] mul_div_b_w = (id_b_signed_r && id_rb_value_r[31]) ? -id_rb_value_r : id_rb_value_r;
    
wire [63:0] mul_opa_a_w = { {32{id_a_signed_r & id_ra_value_r[31]}}, id_ra_value_r };
wire [63:0] mul_opa_b_w = { {32{id_b_signed_r & id_rb_value_r[31]}}, id_rb_value_r };
assign mul_res_w = mul_opa_a_w * mul_opa_b_w;

endmodule
