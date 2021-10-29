module bind_top (
logic         clk_i,
logic         reset_i,
logic [31:0] irdata_i,
logic [31:0] drdata_i,
logic        ird_o,
logic [31:0] iaddr_o,
logic [31:0] daddr_o,
logic [31:0] dwdata_o,
logic  [1:0] dsize_o,
logic  [3:0] dbe_w,
logic        drd_o,
logic        dwr_o,

logic [31:0] id_pc_r,
logic [31:0] id_next_pc_r,
logic        branch_taken_w,
logic [31:0] jump_addr_w,
logic        ex_stall_w
);

   top uut_top (.*);
   bind uut_top tb_top bind_uut_top (.*);

endmodule
