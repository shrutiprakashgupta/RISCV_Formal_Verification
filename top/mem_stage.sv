`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Module Name: 	mem_stage
// Top module:  	top
// Linked modules: 	exe_stage, memory, hazard_detection, wb_stage
//////////////////////////////////////////////////////////////////////////////////

`include"defines.sv"


module mem_stage(
   input             clk_i,
   input             reset_i,
   input      [31:0] ex_alu_res_r, 
   input      [31:0] ex_mem_data_r,
   input             ex_mem_rd_r,
   input             ex_mem_wr_r,
   input             ex_mem_signed_r,
   input       [1:0] ex_mem_size_r,
   input      [31:0] drdata_i,
   input       [4:0] ex_rd_index_w,
                               
   output reg  [4:0] mem_rd_index_w,
   output reg [31:0] mem_wb_alu_result_r,
   output reg [31:0] daddr_o,
   output     [31:0] dwdata_o,
   output      [1:0] dsize_o,
   output            drd_o,
   output            dwr_o,
   output     [31:0] mem_rdata_for_hazard,
   output reg        mem_access_w,
   
   output reg [31:0] mem_rdata_w,
   output      [3:0] dbe_w

);
   
   assign daddr_o  = ex_alu_res_r;
   assign dwdata_o = ex_mem_data_r; 
   assign dsize_o  = ex_mem_size_r; 
   assign drd_o    = ex_mem_rd_r ;
   assign dwr_o    = ex_mem_wr_r ;

   wire [7:0] rdata_byte_w =
      (2'b00 == drdata_i[1:0]) ? drdata_i[7:0] :
      (2'b01 == drdata_i[1:0]) ? drdata_i[15:8] :
      (2'b10 == drdata_i[1:0]) ? drdata_i[23:16] : drdata_i[31:24];

   wire [15:0] rdata_half_w =
      drdata_i[1] ? drdata_i[31:16] : drdata_i[15:0];

   wire [31:0] drdata_o1 =
      (`SIZE_BYTE == ex_mem_size_r) ? { 24'b0, rdata_byte_w } :
      (`SIZE_HALF == ex_mem_size_r) ? { 16'b0, rdata_half_w } : drdata_i;

   wire [31:0] mem_rdata_w_internal = 
      (`SIZE_BYTE == ex_mem_size_r) ? { {24{ex_mem_signed_r & drdata_o1[7]}}, drdata_o1[7:0] } :
      (`SIZE_HALF == ex_mem_size_r) ? { {16{ex_mem_signed_r & drdata_o1[15]}}, drdata_o1[15:0] } : drdata_o1;
   
   assign mem_rdata_for_hazard = mem_rdata_w_internal;

   //wire [31:0] dwdata_w =
   //   (`SIZE_BYTE == ex_mem_size_r) ? {4{ex_mem_data_r[7:0]}} :
   //   (`SIZE_HALF == ex_mem_size_r) ? {2{ex_mem_data_r[15:0]}} : ex_mem_data_r;

   wire [31:0] dwdata_w =
      (`SIZE_BYTE == ex_mem_size_r) ? {24'b0, ex_mem_data_r[7:0]} :
      (`SIZE_HALF == ex_mem_size_r) ? {16'h0, ex_mem_data_r[15:0]} : ex_mem_data_r;

   wire [3:0] dbe_byte_w = 
      (2'b00 == ex_mem_data_r[1:0]) ? 4'b0001 :
      (2'b01 == ex_mem_data_r[1:0]) ? 4'b0010 :
      (2'b10 == ex_mem_data_r[1:0]) ? 4'b0100 : 4'b1000;

   wire [3:0] dbe_half_w =
      ex_mem_data_r[1] ? 4'b1100 : 4'b0011;

   assign dbe_w =
      (`SIZE_BYTE == ex_mem_size_r) ? dbe_byte_w :
      (`SIZE_HALF == ex_mem_size_r) ? dbe_half_w : 4'b1111;

   wire mem_access_r = (ex_mem_rd_r || ex_mem_wr_r);
   
   always @(posedge clk_i or posedge reset_i) begin
      if(reset_i) begin
         mem_rd_index_w      <= 0;
         mem_wb_alu_result_r <= 0;
		 mem_rdata_w         <= 0;
         mem_access_w        <= 0;
      end
      else begin
         mem_rd_index_w      <= ex_rd_index_w;
         mem_wb_alu_result_r <= ex_alu_res_r;
         mem_rdata_w         <= mem_rdata_w_internal;
         mem_access_w        <= mem_access_r;
      end
    end
   
endmodule
