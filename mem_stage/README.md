# Pipeline Memory Stage - [mem_stage.sv](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/mem_stage/mem_stage.sv)

## Functionality
This stage is a controller and interface stage between the execute stage, data memory and the write back stage. The input from the memory (in case of memory read), is further sliced based on the size of data being read - in this stage. However, while writing to the memory, the data is not manipulated here, and a signal is passed to the memory showing what size of data is to be read.

## Neighbouring Stages
It directly connects with execute stage, data_memory and wb_stage (which is removed as it didn't perform any task and added an extra pipeline cycle). 
### Hierarchy
```
mem_stage.tcl
| -- bind_mem_stage.sv
| | -- tb_mem_stage.sv
| | -- defines.sv
| | -- mem_stage.sv
```

## Interface and Testbench
1. Assumption: Read and write cannot happen at the same time
2. Assertion: Checks the signedness and proper value of the output from read stage - based on different types of memory read sizes and sign.

## Errors/Bugs Detected
1. The mem_rdata_for_hazard and mem_rdata are supposed to have the same value - but the former one was defined to be of wire type while the later as register. This caused some of the assertions to fail and thus was identified and rectified.  
