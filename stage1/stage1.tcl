clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
analyze -sv09 stage1.sv tb_stage1.sv bind_stage1.sv 
elaborate -create_related_covers contrapositive -top bind_stage1
 
clock clk_i
reset {reset_i}
