`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////////////////
// Module Name: 	define
// Top module:  	top
// Linked modules:
/////////////////////////////////////////////////////////////////////////////////////////////

`define ALU_ADD   4'd0
`define ALU_SUB   4'd1
`define ALU_AND   4'd2
`define ALU_OR    4'd3
`define ALU_XOR   4'd4
`define ALU_SLT   4'd5
`define ALU_SLTU  4'd6
`define ALU_SHL   4'd7
`define ALU_SHR   4'd8
`define ALU_MULL  4'd9
`define ALU_MULH  4'd10
`define ALU_DIV   4'd11
`define ALU_REM   4'd12
`define ALU_NPC   4'd13
`define ALU_AUIPC 4'd14

`define ST_RESET     2'd0
`define ST_LOW       2'd1
`define ST_HIGH      2'd2
`define ST_UNALIGNED 2'd3

`define BR_NONE   3'd0
`define BR_JUMP   3'd1
`define BR_EQ     3'd2
`define BR_NE     3'd3
`define BR_LT     3'd4
`define BR_GE     3'd5
`define BR_LTU    3'd6
`define BR_GEU    3'd7

`define SIZE_BYTE 2'd0
`define SIZE_HALF 2'd1
`define SIZE_WORD 2'd2

`define PC_SIZE 6'd32
`define RESET_SP 32'h2000
