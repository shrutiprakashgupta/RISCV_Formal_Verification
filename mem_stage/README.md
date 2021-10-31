# Pipeline Memory Stage - [hazard_detection.sv](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/mem_stage/mem_stage.sv)

## Functionality
This stage is a controller and interface stage between the execute stage, data memory and the write back stage. The input from the memory (in case of memory read), is further sliced based on the size of data being read - in this stage. However, while writing to the memory, the data is not manipulated here, and a signal is passed to the memory showing what size of data is to be read.

## Neighbouring Stages
It directly connects with execute stage, data_memory and wb_stage.

## Interface and Testbench
1. Assumption: Read and write cannot happen at the same time
2. Assertion: Checks the signedness and proper value of the output from read stage - based on different types of memory read sizes and sign.
