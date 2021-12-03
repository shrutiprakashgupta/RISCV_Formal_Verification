module memory (
	input 			clk_i,
	input 			reset_i,
	input  [31:0]	daddr_i,
	input  [31:0]	dwdata_i,
	output [31:0]	drdata_o,
	input   [1:0]	dsize_i,
	input 			drd_i,
	input 			dwr_i,  
	input   [3:0]	dbe_w
);

	reg [31:0]	data_mem [31:0]; //Size reduced. as the actual size will not be needed for verification
	wire [7:0]  data_b [3:0];
	wire [15:0] data_w [1:0];
	wire [31:0] data_in;
	
	assign drdata_o 		= drd_i ? data_mem[daddr_i] : 32'b0;
	assign data_b[0] 		= dbe_w[0] ? dwdata_i[7:0] : '{8{1'b0}};
	assign data_b[1] 		= dbe_w[1] ? dwdata_i[15:8] : '{8{1'b0}};
	assign data_b[2] 		= dbe_w[2] ? dwdata_i[23:16] : '{8{1'b0}};
	assign data_b[3] 		= dbe_w[3] ? dwdata_i[31:24] : '{8{1'b0}};
	assign data_w[0] 		= (dbe_w[1:0] == 2'b11) ? dwdata_i[15:0] : '{16{1'b0}};
	assign data_w[1] 		= (dbe_w[3:2] == 2'b11) ? dwdata_i[31:16] : '{16{1'b0}};
	assign data_in 			= (dsize_i == `SIZE_BYTE) ? {data_b[3], data_b[2], data_b[1], data_b[0]} : (dsize_i == `SIZE_HALF) ? {data_w[1], data_w[0]} : dwdata_i; 
	integer i;

	always @(posedge clk_i) begin
		if(reset_i) begin
			for (i=0; i<32; i=i+1) begin
				data_mem[i] <= 32'b0;
			end
		end
		else begin
			if(dwr_i) begin
				data_mem[daddr_i] <= data_in;
			end
		end
	end

endmodule 
