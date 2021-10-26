`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Top module:		top
// Module Name: 	hazard_detection
// Linked modules: 	stage1, exe_stage, mem_stage
//////////////////////////////////////////////////////////////////////////////////

module hazard_detection(
	input         clk_i,
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
	
	output reg    ex_hazard_w_a,
	output reg    ex_hazard_w_b,
	output reg    mem_hazard_w_a,
	output reg    mem_hazard_w_b,
	output reg [31:0] rd_value_r,      
	output reg [31:0] exe_ra_r,
	output reg [31:0] exe_rb_r
);

    wire ex_hazard_w_a_w;
    wire ex_hazard_w_b_w;
    wire mem_hazard_w_a_w;
    wire mem_hazard_w_b_w;
    wire [31:0] rd_value_w;
    wire [31:0] exe_ra_w;
    wire [31:0] exe_rb_w;
    
    assign ex_hazard_w_a_w  = reset_i      ? 0 : (ex_rd_index_r != 5'd0) && (id_ra_index_w == ex_rd_index_r );
    assign ex_hazard_w_b_w  = reset_i      ? 0 : (ex_rd_index_r != 5'd0) && (id_rb_index_w == ex_rd_index_r) ;
    assign rd_value_w       = mem_access_w ? mem_rdata_w : mem_wb_alu_result_r;
    assign mem_hazard_w_a_w = reset_i      ? 0 : (mem_rd_index_w != 5'd0) && (id_ra_index_w == mem_rd_index_w );
    assign mem_hazard_w_b_w = reset_i      ? 0 : (mem_rd_index_w != 5'd0) && (id_rb_index_w == mem_rd_index_w );
        
    assign exe_ra_w = reset_i  ? 32'b0 : ex_hazard_w_a_w ? ex_alu_res_r : ( mem_hazard_w_a_w ? rd_value_w : id_ra_value_r);
    assign exe_rb_w = reset_i  ? 32'b0 : ex_hazard_w_b_w ? ex_alu_res_r : ( mem_hazard_w_b_w ? rd_value_w : id_rb_value_r);
    
    
   always @(posedge clk_i or posedge reset_i) begin
      if(reset_i) begin
         ex_hazard_w_a  <= 0;
         ex_hazard_w_b  <= 0;
         mem_hazard_w_a <= 0;
         mem_hazard_w_b <= 0;
         rd_value_r     <= 32'b0;
         exe_ra_r       <= 32'b0;
         exe_rb_r       <= 32'b0;
      end
      else begin
         ex_hazard_w_a  <= ex_hazard_w_a_w;
         ex_hazard_w_b  <= ex_hazard_w_b_w;
         mem_hazard_w_a <= mem_hazard_w_a_w;
         mem_hazard_w_b <= mem_hazard_w_b_w;
         rd_value_r     <= rd_value_w;
         exe_ra_r       <= exe_ra_w;
         exe_rb_r       <= exe_rb_w;
      end
   end
endmodule
