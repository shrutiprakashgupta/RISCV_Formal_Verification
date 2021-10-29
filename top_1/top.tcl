clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
analyze -sv09 top.sv hazard_detection.sv instruction_memory.sv stage1.sv exe_stage.sv adder.sv multiplier.sv divider.sv shifter.sv mem_stage.sv memory.sv wb_stage.sv register_file.sv tb_top.sv bind_top.sv
elaborate -create_related_covers contrapositive -top bind_top
 
clock clk_i
reset {reset_i}
