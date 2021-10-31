clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
analyze -sv09 hazard_detection.sv tb_hazard_detection.sv bind_hazard_detection.sv 
elaborate -create_related_covers {precondition witness contrapositive} -top bind_hazard_detection

clock clk_i
reset {reset_i}
