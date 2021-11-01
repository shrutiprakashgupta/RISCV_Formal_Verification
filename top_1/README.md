# Combined Verification - Stage1
The testbench used is the same as that for individual stage1. All of the assumptions except those related the instruction and data memory data values are kept - as these as quite large modules, thus it is not a good idea to keep the RTL in the test environment. 

# Errors/Bugs Detected
The write back stage is seen here as taking one extra cycle, and is further removed. The register file is clocked and thus now it works as the 4th stage in pipeline. The write back stage was simply forwarding the signals and thus removing it did not cause any major change. [WB_Extra](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/top_1/result/wb_stage_extra.png)

# Tests Passed
All of the assertions pass. Some of the covers in special (more complex) cases - like division operation with stall signal and branch or jump instruction, are added here. The signal files (.sig) are included which can be directly loaded in the waveform viewing window to get the relevant signals only - for easier debug. All of this is included in the folder result. 
