# Pipeline Execute Stage - [exe_stage.sv](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/exe_stage/exe_stage.sv) 
## Functionality
It is the computational stage, which takes the operands and the operation commands from the ID/IF stage and performs the computation. As the pipelined processor is supported with data forwarding, a choice has to be made between the current operands, data from the execute stage and the data from memory stage, so as to be passed to the execute stage for computation. However, this is taken care by the hazard detection stage, thus the input to the execute stage is well-defined. The testbench considers the values of the operand and the operation type to decide whether the branch should be taken and what should be the output from the execute stage.

## Neighbouring Stages
It gets it's inputs from the stage1 and hazard_detection stages. It then processes them with the help of child stages - adder, shifter, multiplier and divider. It feeds to the memory stage and hazard_detection stage back. 
### Hierarchy
```
exe_stage.tcl <br>
| -- bind_exe_stage.sv <br>
| | -- tb_exe_stage.sv <br>
| | -- defines.sv <br>
| | -- exe_stage.sv <br>
| | | -- adder.sv <br>
| | | -- shifter.sv <br>
| | | -- multiplier.sv <br>
| | | -- divider.sv 
```

## Interface & Testbench
1. input **clk_i**
- Description: Global clock signal 
- Assumptions: -
- Note/Remark: All assertions, assumptions and covers are triggered at this clock signal (positive edge).
2. input **reset_i**
- Description: Global reset signal
- Assumptions: -
- Note/Remark: All assumptions and assertions are sensitive to the reset signal & are disabled when reset is asserted. 
3. input **[3:0] id_alu_op_r**
- Description: The instruction type - including R-type, I-type, L-Type and S-Type 
- Assumptions: `prop_alu_op_types`
- Note/Remark: The valid ALU instructions lie between 0 to 14 only, while the 4-bit signal can have value upto 15, thus this constraint is applied. 
4. input **[31:0] id_ra_value_r**, **[31:0] id_rb_value_r**
- Description: The operand values, after deciding between the original register values and the feedback values.
- Assumptions: -
- Note/Remark: Any 32 bit value can be passed, thus no restriction. However, in case of immediate instructions, this value is restricted to 12-bits (in max), while rest of the bits are 0s, but as the assertions converge over all combinations, thus for simplifying the constraints, any 32-bit value is considered in general. 
5. input **id_a_signed_r**
- Description: Signal is held high if the operand 1 is to be considered as being signed. 
- Assumptions: `prop_val_signed_a` 
- Note/Remark: The signed operands are supported by selected instructions, thus this constraint is there. 
6. input **id_b_signed_r**
- Description: Signal is held high if the operand 2 is to be considered as being signed.
- Assumptions: `prop_val_signed_b`
- Note/Remark: Same as previous assumption. 
7. input **[4:0] id_rd_index_r**
- Description: The index of the destination register.
- Assumptions: -
- Note/Remark: Any 5-bit value is valid.
8. input **[31:0] id_imm_r**
- Description: The value of immedate operand.
- Assumptions: - 
- Note/Remark: Although the immediate operands are not 32-bit and their size and value varies with the instruction type, the whoel 32-bit values are allowed. This is done to simplify the constraints, and also as no assertion fails due to this larger space of input values allowed, thus no extra assumptions are required.
9. input **id_op_imm_r**
- Description: The type of immediate operations.
- Assumptions: `prop_imm_opr`
- Note/Remark: As the immediate operands are supported by selected instructions, thus this constraint is used. Also, the instructions of I-type, S-Type, L-Type and B-Type are exclusive, while the testbench removes the first stage and thus the signals are driven independently. This can cause a branch instruction to be there while the original instruction is 
10. input **[31:0] id_pc_reg**
- Description: The current PC value passed to the execute stage from the stage 1.
- Assumptions: `inc_id_pc_r`,`jump_id_pc_r`, `freeze_id_pc_r`
- Note/Remark: The PC signal is driven independently by the testbench and thus there is no guarentee by default that it will be incremented properly, or changed to the correct value on jump. Thus these assumptions are included to ensure that in case of branch the PC update is correct, in case of stall the PC doesn't change and otherwise it always increments by 4. 
12. input **[31:0] id_next_pc_r**
- Description: The next_pc value passed from stage 1 to execute stage.
- Assumptions: `prop_next_pc_val`
- Note/Remark: As mentioned in the previous stage TB, the pc_next value is always one step (i.e. 4) ahead of current PC. This is ensured with the assumption.
13. input **id_reg_jump_r**
- Description: The signal goes high when the PC should jump to the address taken from a register on branch hit. 
- Assumptions: `prop_reg_jump_instr`
- Note/Remark: This signal should go high only in the case of a specific instruction, thus this constraint ensures that the id_reg_jump_r doesn't get raised randomly.
14. input **[2:0] id_branch_r**
- Description: The type of branch instruction.
- Assumptions: `prop_branch_ex`, `prop_load_store_ex` 
- Note/Remark: The B-Type instruction is exclusive of L-Type, I-Type and S-Type instructions. Thus this constraint ensures that the branch taken instruction type remains insignificant while any other instruction type is there, or while branch instruction is there, the memory read and write are held low.  
15. input **id_mem_rd_r**, **id_mem_wr_r**
- Description: Memory read and write signal.
- Assumptions: `prop_load_store_ex`, `property_load_or_store`
- Note/Remark: The load and store instructions are also exclusive to other instructions and to each other. 
16. input **[1:0] id_mem_size_r**, **id_mem_signed_r**
- Description: Size of the memory being read or written.  
- Assumptions: -
- Note/Remark: No hard constraints.
17. output **reg branch_taken_w**
- Description: The signal is held high in case of branch hit. 
- Assertions: `prop_beq_fail`,`prop_beq_pass`,`prop_bne_fail`,`prop_bne_pass`,`prop_blt_fail`,`prop_blt_pass`,`prop_bge_fail`,`prop_bge_pass`,`prop_bltu_fail`,`prop_bltu_pass`,`prop_bgeu_fail`,`prop_bgeu_pass`,  
- Note/Remark: The branch taken should go high only when a branch instruction is issued and the conditions hold good. A function named taken is thus created, which takes the current values of the signals like operands, operation, immediate value and the signal detecting wether the register operands are to be taken or the immediate value, and gives a binary value as output - which is 1 when branch should be taken and 0 otherwise. This is further used to put the assertion on the value of branch_taken_w signal on the next cycle. 
18. output **reg [31:0] jump_addr_w**
- Description: The address to which PC should jump in case of branch hit.  
- Assertions:  -
- Note/Remark: Direct assignment of value selected between the register value and the immediate value being added to the current PC, thus no extra assertion needed. 
19. output **reg [4:0] ex_rd_index_r**
- Description: Destination address from the execute stage.  
- Assertions:  -
- Note/Remark: Direct signal forwarding, thus no assertion here. 
20. output **reg [31:0] ex_alu_res_r**
- Description: The result from the alu. 
- Assertions: `prop_add`, `prop_sub`, `prop_and`, `prop_or`, `prop_xor`, `prop_slt`, `prop_sltu`, `prop_shl`, `prop_mull`, `prop_mulh`, `prop_div` 
- Note/Remark: A function named alu_out is defined in the testbench which takes in the current operands, immediates, and the operation code to calculate the output which is expected from the execute stage in ideal case. This value is directly used to assert the ex_alu_res_r signal's value. This assertion is the most powerful one, as it checks every signal possible instruction and thus provides confidence on the overall working of execute stage. 
- Result: The assertion converges for all instructions except multiply and division. This is due to the high complexity of these instructions (being 32-bit each). However, the depth reached by the prover is sufficient. It is further explained here:
- `prop_mull`, `prop_mulh` - depth reached = 5. The operation takes single cycle for completion, thus it is sufficient.
- `prop_div` - depth reache = 170. The instruction takes 32 cycles for one computation, and one extra cycle to load the next instruction - this is considered in writing the assertion as well, and thus the output is checked after 32 cycles only. Also, the depth is sufficient. 
21. output **reg [31:0] ex_mem_data_r**, **reg ex_mem_rd_r**, **reg ex_mem_wr_r**, **reg ex_mem_signed_r**, **reg [1:0] ex_mem_size_r**, 
- Description: The signals forwarded to the memory stage concerning load and store instructions.   
- Assertions:  -
- Note/Remark: Direct assignments from the execute stage to these signals - as execute stage is used only to put one cycle delay for the signals (or it's like data forwarding between two non-consecutive stages in pipeline). Thus no hard constrained on these signals is needed. 
22. output **ex_stall_w**
- Description: The stall signal from execute stage to stage1, restricting the progress of PC when division instruction is in progress.
- Assertions:  -
- Note/Remark: The direct logic of ex_stall_w is div_request is raised and another divide is not in progress. Thus there is not any hard assertion to be tested.

## Note
The iaddr_o or PC signal passed to the instruction memory is sometimes held constant (stalled). However, in case of the prover, the signals are driven independently, and there is no relation (or constraint) between the PC and instruction (or here the signals computed by decoding instruction). Thus `prop_freeze_` assumptions are used to bind these signals to the pc address and stall them as well with the PC value.  
    
## Child Stages
The behaviour of the children stages are verified with the assertions put on the execute stage output and thus there is no need to write separate testbenches for each of them. 

## Errors/Bugs Detected
1. Division and Remainder operations work giving wrong output in the following cases 
- stall signal not affecting PC : further added to the logic of stage1
- exceptional cases : when the divisor is zero, consuming 32 cycles in division is not a wise choice, also the output coming out after 32 cycles was not correct. This was further rectified by making RTL changes in divider module.
