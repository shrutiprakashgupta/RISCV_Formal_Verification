`include"defines.sv"

module tb_mem_stage(
	input        clk_i,
	input        reset_i,
	input [31:0] ex_alu_res_r, 
	input [31:0] ex_mem_data_r,
	input        ex_mem_rd_r,
	input        ex_mem_wr_r,
	input        ex_mem_signed_r,
	input  [1:0] ex_mem_size_r,
	input [31:0] drdata_i,
	input  [4:0] ex_rd_index_w,
	                            
	input  [4:0] mem_rd_index_w,
	input [31:0] mem_wb_alu_result_r,
	input [31:0] daddr_o,
	input [31:0] dwdata_o,
	input  [1:0] dsize_o,
	input        drd_o,
	input        dwr_o,
	input [31:0] mem_rdata_for_hazard,
	input        mem_access_w,
	
	input [31:0] mem_rdata_w,
	input  [3:0] dbe_w

);
   
	//Restricting stimulus
	//Read and Write cannot happen simultaneously, due to the nature of instructions 
	property rd_or_wr;
		@(posedge clk_i) disable iff (reset_i) !(ex_mem_rd_r & ex_mem_wr_r);
	endproperty
	
	valid_rd_or_wr: assume property (rd_or_wr);
	
	
	//Testing Output - Assertions on Output
	//--------------------------------------------daddr_o---------------------------------------------
	//Directly assigned the input coming from the execute stage, thus memory
	//alignement not guarenteed. This can be prevented from causing an issue in
	//the memory block itself - Thus no explicit assertion 
	
	//--------------------------------------------dwdata_o--------------------------------------------
	//Data passed directly, this would require byte-writability in memory  
	
	//-----------------------------------------mem_rdata_for_hazard-----------------------------------
	//--------------------------------------------mem_rdata_w-----------------------------------------
	//Check sign extension or zero padding based on the read flag status, and
	//the data size
	
	//Signed byte read
	property signed_byte_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_BYTE) & (ex_mem_rd_r) & (ex_mem_signed_r) |=> (mem_rdata_w[31:8] == {24{mem_rdata_w[7]}}); 
	endproperty
	
	prop_signed_byte_read: assert property (signed_byte_read);
	
	//Unsigned byte read
	property unsigned_byte_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_BYTE) & (ex_mem_rd_r) & (!ex_mem_signed_r) |=> (mem_rdata_w[31:8] == 24'b0); 
	endproperty
	
	prop_unsigned_byte_read: assert property (unsigned_byte_read);
	
	//Signed hlaf read
	property signed_half_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_HALF) & (ex_mem_rd_r) & (ex_mem_signed_r) |=> (mem_rdata_w[31:16] == {16{mem_rdata_w[15]}}); 
	endproperty
	
	prop_signed_half_read: assert property (signed_half_read);
	
	//Unsigned half read
	property unsigned_half_read;
		@(posedge clk_i) disable iff (reset_i) (ex_mem_size_r == `SIZE_HALF) & (ex_mem_rd_r) & (!ex_mem_signed_r) |=> (mem_rdata_w[31:16] == 16'h0); 
	endproperty
	
	prop_unsigned_half_read: assert property (unsigned_half_read);

endmodule
