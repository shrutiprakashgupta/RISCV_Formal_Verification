clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
analyze -sv09 mem_stage.sv tb_mem_stage.sv bind_mem_stage.sv 
elaborate -create_related_covers {precondition witness contrapositive} -top bind_mem_stage
 
clock clk_i
reset {reset_i}
