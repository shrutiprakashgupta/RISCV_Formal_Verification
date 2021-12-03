`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	divider
// Top module:  	top
// Linked modules: 	exe_stage
////////////////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"

module divider(
input clk_i,
input reset_i,

input [3:0] id_alu_op_r,
input mul_div_negative_w,
input [31:0] mul_div_a_w,
input [31:0] mul_div_b_w,

output [31:0] div_quotient_w,
output [31:0] div_remainder_w,
output ex_stall_div_w
    );
    
    reg         div_busy_r;
    reg         div_ready_r;
    reg   [4:0] div_count_r;
    reg  [31:0] div_rem_r;
    reg  [31:0] div_quot_r;
    reg  [31:0] div_b_val;
    reg         div_neg;

    wire [32:0] div_sub_w = { 1'b0, div_rem_r[30:0], div_quot_r[31] } - { 1'b0, div_b_val };
    wire div_request_w  = (`ALU_DIV == id_alu_op_r || `ALU_REM == id_alu_op_r);
    wire [31:0] div_out_spc = (mul_div_b_w == 32'd0) ? 32'hffff_ffff : (mul_div_a_w == 32'b0) ? 32'd0 : (mul_div_b_w == mul_div_a_w) ? 32'd1 : 32'd0;
    wire div_spc_case = (mul_div_b_w == 32'd0) || (mul_div_a_w == 32'b0) || (mul_div_b_w == mul_div_a_w);
    
    assign div_quotient_w  = div_neg ? -div_quot_r : div_quot_r;
    assign div_remainder_w = div_neg ? -div_rem_r : div_rem_r;
    
    always @(posedge clk_i) begin
      if (reset_i) begin
        div_busy_r  <= 1'b0;
        div_ready_r <= 1'b0;
        div_count_r <= 5'd0;
        div_quot_r  <= 32'h0;
        div_rem_r   <= 32'h0;
        div_b_val   <= 32'h0;
        div_neg     <= 0;
      end else begin
        if (div_busy_r) begin
          div_count_r <= div_count_r - 5'd1;
          div_quot_r  <= { div_quot_r[30:0], !div_sub_w[32] };
    
          if (div_sub_w[32])
            div_rem_r <= { div_rem_r[30:0], div_quot_r[31] };
          else
            div_rem_r <= div_sub_w[31:0];
    
          if (div_count_r == 5'd0) begin
            div_busy_r  <= 1'b0;
            div_ready_r <= 1'b1;
          end
    
        end else if (div_ready_r) begin
          div_ready_r <= 1'b0;
    
        end else if (div_request_w) begin
            if(div_spc_case) begin
                div_count_r <= 5'd0;
                div_busy_r  <= 1'b0;
                div_quot_r  <= div_out_spc;
                div_rem_r   <= 32'd0;
                div_ready_r <= 1'b1;
            end
            else begin
                div_count_r <= 5'd31;
                div_busy_r  <= 1'b1;
                div_quot_r  <= mul_div_a_w;
                div_rem_r   <= 32'h0;
                div_b_val   <= mul_div_b_w;
                div_neg     <= mul_div_negative_w;
            end
        end
      end
    end
    
    
    assign ex_stall_div_w = div_request_w && !div_ready_r;
endmodule
