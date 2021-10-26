module tb_hazard_detection (
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
	
	input         ex_hazard_w_a,
	input         ex_hazard_w_b,
	input         mem_hazard_w_a,
	input         mem_hazard_w_b,
	input  [31:0] rd_value_r,   
	input  [31:0] exe_ra_r,
	input  [31:0] exe_rb_r   
);

	//Restricting stimulus - No strict restriction but just to observe the value being passed and the source related  
	property distinct_val_ra;
	   @(posedge clk_i) disable iff (reset_i) !(id_ra_value_r inside {id_rb_value_r, ex_alu_res_r, mem_wb_alu_result_r, mem_rdata_w});
	endproperty
	
	prop_distinct_val_ra: assume property (distinct_val_ra);
	
	property distinct_val_rb;
	   @(posedge clk_i) disable iff (reset_i) !(id_rb_value_r inside {id_ra_value_r, ex_alu_res_r, mem_wb_alu_result_r, mem_rdata_w});
	endproperty
	
	prop_distinct_val_rb: assume property (distinct_val_rb);
	
	property distinct_val_ex;
	   @(posedge clk_i) disable iff (reset_i) !(ex_alu_res_r inside {id_ra_value_r, id_rb_value_r, mem_wb_alu_result_r, mem_rdata_w});
	endproperty
	
	prop_distinct_val_ex: assume property (distinct_val_ex);
	
	property distinct_val_mem_ex;
	   @(posedge clk_i) disable iff (reset_i) !(mem_wb_alu_result_r inside {id_ra_value_r, id_rb_value_r, ex_alu_res_r, mem_rdata_w});
	endproperty
	
	prop_distinct_val_mem_ex: assume property (distinct_val_mem_ex);
	
	property distinct_val_mem;
	   @(posedge clk_i) disable iff (reset_i) !(mem_rdata_w inside {id_ra_value_r, id_rb_value_r, ex_alu_res_r, mem_wb_alu_result_r});
	endproperty
	
	prop_distinct_val_mem: assume property (distinct_val_mem);
	
	//Debugging and Understanding the code 
	//LW R2 0[R3]
	//ADD R3 R1 R4
	//ADD R5 R3 R1
	property ex_hazard_mem_access;
	   @(posedge clk_i) disable iff (reset_i) (ex_rd_index_r == 5'd1) ##1(id_ra_index_w == 5'd3) && (ex_rd_index_r == 5'd3) && (mem_rd_index_w == 5'd2) && (mem_access_w) ##3 1'b1;
	endproperty
	
	prop_hazard_ex_mem_access: cover property (ex_hazard_mem_access);
	
	//Checking output - Assertions 
	//Dependency on execute
	property ex_hazard_a;
	   integer ra_val_1;
	   @(posedge clk_i) disable iff (reset_i) (((id_ra_index_w == ex_rd_index_r) && (id_ra_index_w != 5'd0)), ra_val_1 = ex_alu_res_r) |=> (exe_ra_r == ra_val_1);
	endproperty
	
	prop_ex_hazard_a: assert property (ex_hazard_a);
	
	//Dependency on memorystage - without memory access
	property mem_n_access_hazard_a;
	   integer ra_val_2;
	   @(posedge clk_i) disable iff (reset_i) (((id_ra_index_w != ex_rd_index_r) && (id_ra_index_w == mem_rd_index_w) && (!mem_access_w) && (id_ra_index_w != 5'd0)), ra_val_2 = mem_wb_alu_result_r) |=> (exe_ra_r == ra_val_2);
	endproperty
	
	prop_mem_n_access_hazard_a: assert property (mem_n_access_hazard_a);
	
	//Dependency on memorystage - with memory access
	property mem_access_hazard_a;
	   integer ra_val_3;
	   @(posedge clk_i) disable iff (reset_i) (((id_ra_index_w != ex_rd_index_r) && (id_ra_index_w == mem_rd_index_w) && (mem_access_w) && (id_ra_index_w != 5'd0)), ra_val_3 = mem_rdata_w) |=> (exe_ra_r == ra_val_3);
	endproperty
	
	prop_mem_access_hazard_a: assert property (mem_access_hazard_a);
	
	//Dependency on execute
	property ex_hazard_b;
	   integer rb_val_1;
	   @(posedge clk_i) disable iff (reset_i) (((id_rb_index_w == ex_rd_index_r) && (id_rb_index_w != 5'd0)), rb_val_1 = ex_alu_res_r) |=> (exe_rb_r == rb_val_1);
	endproperty
	
	prop_ex_hazard_b: assert property (ex_hazard_b);
	
	//Dependency on memorystage - without memory access
	property mem_n_access_hazard_b;
	   integer rb_val_2;
	   @(posedge clk_i) disable iff (reset_i) (((id_rb_index_w != ex_rd_index_r) && (id_rb_index_w == mem_rd_index_w) && (!mem_access_w) && (id_rb_index_w != 5'd0)), rb_val_2 = mem_wb_alu_result_r) |=> (exe_rb_r == rb_val_2);
	endproperty
	
	prop_mem_n_access_hazard_b: assert property (mem_n_access_hazard_b);
	
	//Dependency on memorystage - with memory access
	property mem_access_hazard_b;
	   integer rb_val_3;
	   @(posedge clk_i) disable iff (reset_i) (((id_rb_index_w != ex_rd_index_r) && (id_rb_index_w == mem_rd_index_w) && (mem_access_w) && (id_rb_index_w != 5'd0)), rb_val_3 = mem_rdata_w) |=> (exe_rb_r == rb_val_3);
	endproperty
	
	prop_mem_access_hazard_b: assert property (mem_access_hazard_b);

endmodule
