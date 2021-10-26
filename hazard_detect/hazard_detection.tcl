clear -all
jasper_scoreboard_3 -init
set_elaborate_single_run_mode off
#analyze -sv09 -ignore_translate_off  +define+XBUF_DISABLE +define+SVA_LIB_SVA2009+ASSERT_ON datamemory.vs sb_req.vs assert_top_datamemory.vs 
analyze -sv09 hazard_detection.sv tb_hazard_detection.sv bind_hazard_detection.sv 
elaborate -create_related_covers {precondition witness contrapositive} -top bind_hazard_detection
#set_visualize_preload_signal_list hazard_detect.sig

clock clk_i
reset {reset_i}
