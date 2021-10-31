clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
analyze -sv09 exe_stage.sv adder.sv multiplier.sv shifter.sv divider.sv tb_exe_stage.sv bind_exe_stage.sv 
# disable_auto_bbox is used to disable the black boxing of multiplier and division modules
# Jasper by default black boxes these modules due to their high complexity, if the disable_auto_bbox flag is not used
elaborate -create_related_covers {contrapositive precondition witness} -top bind_exe_stage -disable_auto_bbox
 
clock clk_i
reset {reset_i}
