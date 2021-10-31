# Pipeline Stage 1 - [stage1.sv](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/stage1/stage1.sv) 
## Functionality
It is the combined Instruction fetch and decode stage. It controls the PC value, which is directly fed to the instruction memory and the corresponding instruction is read. It also decodes the instructions for the execute stage. Summing up the PC updations - it is incremented by four in general case, while when a branch instruction is hit, PC jumps to the target address and is held constant while the stall signal is held high from the execute stage. 

## Neighbouring Stages
It directly connects with the instruction memory, hazard detection stage and the execute stage. Instruction memory is purely combinational and read-only, same as hazard detect stage, while the execute stage is one-cycle behind the stage1. 

## Interface & Testbench
1. input **clk_i**
- Description: Global clock signal
- Assumptions: -
- Note/Remark: All assertions, assumptions and covers are triggered at this clock signal (positive edge).
2. input **reset_i**
- Description: Global reset signal
- Assumptions: -
- Note/Remark: All assumptions and assertions are sensitive to the reset signal & are disabled when reset is asserted. 
3. input **[31:0] irdata_i**
- Description: 32-bit Instruction read from the instruction memory. As the memory is combinational in nature, thus the instruction corresponds to the current value of PC (which is updated on clock edge inside the stage1).
- Assumptions: `valid_instr_types`, `valid_f7_types`, `valid_btype_instr`, `valid_ltype_instr`, `valid_stype_instr`, `valid_itype1_instr`, `valid_itype2_instr`, `valid_rtype2_instr` 
- Note/Remark: Supported instruction types are - R-Type(20), I-Type(9), L-Type(5), S-Type(3), B-Type(8). The core instructions are listed here:  
`ALU_ADD`, `ALU_SUB`, `ALU_AND`, `ALU_OR`, `ALU_XOR`, `ALU_SLT`, `ALU_SLTU`, `ALU_SHL`, `ALU_SHR`, `ALU_MULL`, `ALU_MULH`, `ALU_DIV`, `ALU_REM`, `ALU_NPC`, `ALU_AUIPC`, `BR_NONE`, `BR_JUMP`, `BR_EQ`, `BR_NE`, `BR_LT`, `BR_GE`, `BR_LTU`, `BR_GEU`   
The assumptions ensure only valid instructions are passed to the stage1. As modelling instruction_memory for the verification purpose would be cumbersome due to it's large size, it is black boxed. The instruction signal is directly driven by the testbench.
- Assumptions: `prop_if_stall`  
- Note: When the instruction memory is present in the pipeline, then there is a one-on-one mapping between the PC value and instruction, however, when the testbench drives the instruction signal, this is not followed by default. Thus adding this assuption to ensure that instruction value does not change while the PC value is held constant (in case of ex_stall signal being held high). 

4. input **branch_taken_w**
- Description: The signal is passed from the execute stage and is held high when branch instruction is hit, this is a trigger to change the PC value to the target value. In the stage1, branch_taken_w signal is used to decide the next PC value, and in case of branch hit, it triggers a NOP to be passed in the pipeline through the execute stage.
- Assumptions: `prop_br_stall_div`, `valid_br_taken`
Note: Branch hit can be seen only when a branch instruction is passed from the first stage and then the conditional statement (not applicable for Jump instruction) is met. Also, in case of branch hit a NOP is pushed in pipeline, thus no two branch instructions can be hit consecutively. This would be the default case in the pipeline (assuming proper functionality), but it is not so in the testbench. Thus, the valid_br_taken assumption is included. Also, while a division operation is in progress, the output from the execute stage is concerned with DIV only, and a branch hit cannot occur meanwhile. The prop_br_stall_div ensures this in testbench.

5. input **[31:0] jump_addr_w**
- Description: The address to which PC needs to jump after a branch hit 
- Assumptions: -
- Note/Remark: This address is decided in the execute stage and thus assuming the proper functionality of rest of the stages while verifying stage1, it is not constrained or verified for having proper value.
Moreover, the maximum range to which PC can jump is decided by the size of the offset - which is restricted by the instruction format, so no extra check required. 

6. input **ex_stall_w**
- Description: The stall signal coming from the execute stage while the division instruction remains in progress. This freezes the PC and allows the next instruction to be issued only when the division is complete. 
- Assumptions: `valid_ex_stall_div`, `valid_ex_stall_n_div`
- Note/Remark: This stall signal is one-cycle behind (due to being generated in the execute stage). This means that when the input to the stage1 is DIV type, then on the next cycle it goes to the execute stage and the stall signal is pulled high. However, due to pipeline, the next instruction is already read by this time. To rectify this, the stage1 is modified so that it continuously checks if the instruction entering is DIV type so that as soon as it encounters the stall signal being raised, it stalls the PC and proceeds only when division is complete.

7. output **[31:0] id_pc_r**
- Description: The pc signal is stored version of the signal passed to instruction_memory
- Assertions: `prop_pc_delay`,`word_align` 
- Note/Remark: The pc value passed to the instruction memory is stored and passed to the other stages. The same is verified with prop_pc_delay. Also, PC should always be word aligned. Instead of the misaligned exception, here the last two bits are forced to zero - which is not the case as per the original ISA.

8. output **[31:0] id_next_pc_r**
- Description: The next PC value assuming no branch hit is passed from this signal. It is used as the execute stage data output, in case of NPC instruction (i.e. used with jump and link instruction) in the execute stage. 
- Assertion: `next_pc_val`,`word_align` 
- Note/Remark: It always remains one step behind the current PC, and even in the case of branch hit, it is decided from the original PC value which is further corrected on the next cycle - thus a general assertion demanding next_pc as pc + 4 is sufficient for both branch and non-branch case. Also, being PC value, it should be word aligned.

9. output **[4:0] id_rd_index_r, [4:0] addr_1, [4:0] addr_2**
- Description: The register addresses for the operand and destination registers.
- Assertion:   -
- Note/Remark: As the instruction signal is sliced to assign the values of these address registers, there is no scope of error and no specific assertion attached to it. 

10. output **id_a_signed_r, id_b_signed_r**
- Description: The signals direct if the values of the operands are signed or unsigned
- Assertion:   -
- Note/Remark: As the instruction signal is sliced to assign the values of these sign registers, there is no scope of error and no specific assertion attached to it. 

11. output  **[3:0] id_alu_op_r**
- Description: The signal is one-on-one map to the R-type instructions
- Assertion:   -
- Note/Remark: As the instruction signal is used with a case statement to assign the values of this signal, there is no scope of error and no specific assertion attached to it. 

12. output **[31:0] id_imm_r, id_op_imm_r**
- Description: These signals correspond to the immediate instruction type and the immediate value
- Assertion:   -
- Note/Remark: As the instruction signal is sliced to assign the values of these sign registers, there is no scope of error and no specific assertion attached to it. 

13. output **id_mem_rd_r, id_mem_wr_r, id_mem_signed_r, [1:0] id_mem_size_r**
- Description: These signals correspond to the data memory - read/write, signedness of data and size of data to be read (BYTE, WORD or DOUBLE_WORD)
- Assertion:   -
- Note/Remark: As the instruction signal is sliced to assign the values of these sign registers, there is no scope of error and no specific assertion attached to it. 

14. output **[2:0] id_branch_r**
- Description: This signal correspond to the type of branch instruction - one-on-one mapping to the instructions.
- Assertion:   -
- Note/Remark: As the instruction signal is sliced to assign the values of this signal, there is no scope of error and no specific assertion attached to it. 

15. output **id_reg_jump_r**
- Description: This signal goes high if the jump instruction has to take the target value from a register, otherwise the target value is taken from immediate value.
- Assertion:   -
- Note/Remark: As the instruction signal is sliced to assign the values of this signal, there is no scope of error and no specific assertion attached to it. 

16. output **[31:0] iaddr_o, ird_o**
- Description: The pc signal passed to the instruction memory
- Assertions: `pc_inc_prop`, `pc_jump_prop`
- Note/Remark: The pc should increment by 4, unless a branch instruction is there or stall is set high from the execute stage because a divide instruction is in progress. While, in case of branch instruction it should change to the value passed as the branch target. The ird_o signal is like enable signal for the instruction memory and is tied to 1. 
