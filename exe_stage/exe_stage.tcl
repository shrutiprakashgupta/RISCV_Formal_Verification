clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
#analyze -sv09 -ignore_translate_off  +define+XBUF_DISABLE +define+SVA_LIB_SVA2009+ASSERT_ON datamemory.vs sb_req.vs assert_top_datamemory.vs 
analyze -sv09 exe_stage.sv adder.sv multiplier.sv shifter.sv divider.sv tb_exe_stage.sv bind_exe_stage.sv 
#elaborate -create_related_covers {contrapositive precondition witness} -top bind_exe_stage -bbox_mul 65 -bbox_div 33 -bbox_mod 33
elaborate -create_related_covers {contrapositive precondition witness} -top bind_exe_stage -disable_auto_bbox
 
clock clk_i
reset {reset_i}
