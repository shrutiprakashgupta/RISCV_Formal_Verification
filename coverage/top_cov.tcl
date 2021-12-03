clear -all
check_cov -init -model {branch statement expression toggle functional} -toggle_ports_only -exclude_bind_hierarchies
analyze -sv bind_top.sv tb_top.sv top.sv hazard_detection.sv instruction_memory.sv stage1.sv exe_stage.sv adder.sv multiplier.sv divider.sv shifter.sv mem_stage.sv memory.sv wb_stage.sv register_file.sv
elaborate -create_related_covers {precondition witness contrapositive} -top bind_top -disable_auto_bbox
clock clk_i
reset reset_i
prove -all -time_limit 1200s
check_cov -measure
check_cov -report -report_file final_cov.txt
