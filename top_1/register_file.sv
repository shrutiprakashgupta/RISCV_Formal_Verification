module register_file (
	input 			clk_i,
	input 			reset_i,
	input  [4:0]	addr_1,
	input  [4:0]	addr_2,
	input [31:0]	data_in,
	input  [4:0]	data_write_address,
	input 			write_enable_w,
	output [31:0]	out_1,
	output [31:0]	out_2
);

reg [31:0]	reg_file [31:0];

assign out_1 = reg_file[addr_1];
assign out_2 = reg_file[addr_2];
wire 	  we = (data_write_address == 0) ? 1'b0 : write_enable_w; 
integer i;

always @(posedge clk_i) begin
	if(reset_i) begin
		for (i=0; i<32; i=i+1) begin
			reg_file[i] <= 32'b0;
		end
	end
	else begin
		if(we) begin
			reg_file[data_write_address] <= data_in;
		end
	end
end

endmodule 
