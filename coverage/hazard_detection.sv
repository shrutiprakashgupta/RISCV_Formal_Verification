`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Top module:		top
// Module Name: 	hazard_detection
// Linked modules: 	stage1, exe_stage, mem_stage
//////////////////////////////////////////////////////////////////////////////////

module hazard_detection (
   input         reset_i,
   input   [4:0] id_ra_index_w,
   input   [4:0] id_rb_index_w,
   input   [4:0] id_rd_index_r,
   input   [4:0] ex_rd_index_r,
   input   [4:0] mem_rd_index_w,
   
   input  [31:0] id_ra_value_r,
   input  [31:0] id_rb_value_r,
   input  [31:0] ex_alu_res_r,
   input  [31:0] mem_wb_alu_result_r,
   input  [31:0] mem_rdata_w,
   
   input         mem_access_w,
   
   output [31:0] exe_ra_r,
   output [31:0] exe_rb_r
);

    wire ex_hazard_w_a;
    wire ex_hazard_w_b;
    wire mem_hazard_w_a;
    wire mem_hazard_w_b;
    wire [31:0] rd_value_w;
    
    assign ex_hazard_w_a  = reset_i      ? 0 : (ex_rd_index_r != 5'd0) && (id_ra_index_w == ex_rd_index_r );
    assign ex_hazard_w_b  = reset_i      ? 0 : (ex_rd_index_r != 5'd0) && (id_rb_index_w == ex_rd_index_r) ;
    assign rd_value_w     = mem_access_w ? mem_rdata_w : mem_wb_alu_result_r;
    assign mem_hazard_w_a = reset_i      ? 0 : (mem_rd_index_w != 5'd0) && (id_ra_index_w == mem_rd_index_w );
    assign mem_hazard_w_b = reset_i      ? 0 : (mem_rd_index_w != 5'd0) && (id_rb_index_w == mem_rd_index_w );
        
    assign exe_ra_r = reset_i  ? 32'b0 : ex_hazard_w_a ? ex_alu_res_r : ( mem_hazard_w_a ? rd_value_w : id_ra_value_r);
    assign exe_rb_r = reset_i  ? 32'b0 : ex_hazard_w_b ? ex_alu_res_r : ( mem_hazard_w_b ? rd_value_w : id_rb_value_r);
    
endmodule
