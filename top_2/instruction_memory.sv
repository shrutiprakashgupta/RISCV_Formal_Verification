module instruction_memory (
	input  			clk_i,
	input  			reset_i,
	input  [31:0]	iaddr_i,
	input  			ird_i,
	output [31:0]	irdata_o
);

	reg [31:0] data; 

	always @*
		case (iaddr_i[31:2])
			30'h00000000: data = 31'h01111111; 
			30'h00000001: data = 31'h00001101; 
			30'h00000010: data = 31'h10110111; 
			30'h00000011: data = 31'h10011111; 
			30'h00000100: data = 31'h11001101; 
			30'h00000101: data = 31'h11011011; 
			30'h00000110: data = 31'h11111011; 
			30'h00000111: data = 31'h00001111; 
			30'h00001000: data = 31'h11111111; 
			30'h00001001: data = 31'h11011111; 
			 	 default: data = 31'h00000001; 
 		endcase

	assign irdata_o = ird_i ? data : 32'h0;
endmodule
