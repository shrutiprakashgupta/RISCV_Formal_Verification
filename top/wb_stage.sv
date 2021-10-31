`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Module Name: 	wb_stage
// Top module:  	top
// Linked modules: 	mem_stage, register_file
//////////////////////////////////////////////////////////////////////////////////

module wb_stage(
   input             clk_i,
   input             reset_i,
   input       [4:0] mem_rd_index_r,
   input             mem_access_w,
   input      [31:0] mem_wb_alu_result_r,
   input      [31:0] mem_rdata_w,

   output reg  [4:0] rd_index_w,
   output reg [31:0] rd_value_reg,
   output reg        rd_we_w

);

   wire [31:0] rd_value_w = mem_access_w ? mem_rdata_w : mem_wb_alu_result_r;

   always@(posedge clk_i or posedge  reset_i) begin
      if( reset_i ) begin
         rd_index_w   <= 0;
         rd_value_reg <= 0;
         rd_we_w      <= 0;
      end
      else begin
         if(mem_rd_index_r == 5'd0) begin
            rd_we_w      <= 0;
            rd_index_w   <= 0;
            rd_value_reg <= 0;
         end
         else begin
            rd_we_w      <= 1;
            rd_index_w   <= mem_rd_index_r;
            rd_value_reg <= rd_value_w;
         end
      end
   end

endmodule
