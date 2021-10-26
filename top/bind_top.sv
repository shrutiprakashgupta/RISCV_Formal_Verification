module bind_top (
logic        clk_i,
logic        reset_i,
logic [31:0] iaddr_o
);

   top uut_top (.*);
   bind uut_top tb_top bind_uut_top (.*);

endmodule
