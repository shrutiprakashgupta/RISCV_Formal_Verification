# Pipeline Hazard Detection Stage - [hazard_detection.sv](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/hazard_detect/hazard_detection.sv) 
## Functionality
It is a purely combinational stage which takes the inputs (including register indices and values of operands and destination registers) from the stage1, exe_stage and mem_stage, and checks for any hazard cases to be present. If there is any hazard (i.e. the operand register of stage1 is same as the destination register of execute or memory stage), then it passes the value from the corresponding stage, instead of the original operand value - and aids the feedforward process in the pipeline. 

## Neighbouring Stages
It takes inputs from the stage1, exe_stage, data memory stage and the register file. It then decides the correct operand values based on hazardous cases existing and the precedence rules, and feeds the output to the exe_stage.
### Hierarchy
```
hazard_detection.tcl
| -- bind_hazard_detection.sv
| | -- tb_hazard_detection.sv
| | -- defines.sv
| | -- hazard_detection.sv
```

## Testing Combinational block with Formal
As the formal verification tests the model at each clock step, as it progresses over time, the presence of clock signal vital for writing assumptions and assertions. Thus for this purely combinational block, I separated it from the other stages and put a set of registers at its output. This transformation will although affect the timing in pipeline, however for testing individual block, it is harmless. When it is connected back in the pipeline, the registers are removed, ensuring proper timing. 

## Interface & Testbench
1. input **clk_i**
- Description: The global clock signal.
2. input **reset_i**
- Description: The global reset signal.
3. input **[4:0] id_ra_index_w**, **[4:0] id_rb_index_w**, **[4:0] id_rd_index_r**
- Description: The operand and destination register indices.
4. input **[4:0] ex_rd_index_r**, **[4:0] mem_rd_index_w**
- Description: destination register index of curr-1 and curr-2 instruction, i.e. from execute and memory stage.
5. input **[31:0] id_ra_value_r**, **[31:0] id_rb_value_r**, **[31:0] ex_alu_res_r**, **[31:0] mem_wb_alu_result_r**, **[31:0] mem_rdata_w**
- Description: `id_ra_value_r`, `id_rb_value_r` - Values read from register file, `ex_alu_res_r` - output from execute stage, `mem_wb_alu_result_r` - output from execute stage currently in memory stage (i.e. from curr-2 instruction), `mem_rdata_w` - memory stage output. 
6. input **mem_access_w**
- Description: Signal showing whether the memory stage output is data from memory (read/write) or the execute stage output from curr-2 instruction. 
7. output reg **ex_hazard_w_a**, **ex_hazard_w_b**, **mem_hazard_w_a**, **mem_hazard_w_b**
- Description: These signals are included only for the testbench and detect whether these hazards exist. Putting these signals as output simplify the testbench.
8. output reg **[31:0] rd_value_r**      
- Description: Output from the memory stage - decided on the basis of mem_access_w signal.
9. output reg **[31:0] exe_ra_r**, **[31:0] exe_rb_r**
- Description: Execute stage output - decided on the basis of hazard existance.
10. Assumptions: All of the assumptions are forcing the data values to be different for easy tracking of at the output (waveform level). However, these are not hard restrictions. 
11. Assertions: The assertions check if the hazardous cases are being detected or not. 

# Errors/Bugs detected
1. The precedence between data from execute and memory stage, in case both the hazards occur simultaneously was wrong before. The execute stage should get the preference as it corresponds to curr-1 instruction while the memory stage corresponds to curr-2 instruction and will be overwritten by the curr-1 instruction output. 
