# Combined Verification - Hazard Detection 
The testbench used is the same as that for individual hazard_detection stage. All of the assumptions except those related the instruction and data memory data values are kept - as these as quite large modules, thus it is not a good idea to keep the RTL in the test environment. 

# Errors/Bugs Detected
The data from memory stage which is related to the memory (and not the execute stage output from curr-2 instruction), should be read in this specific hazard case - i.e. hazard between stage1 and mem_stage while mem_access is high. While due to the wire and register nature of the signals mem_rdata_for_hazard and mem_rdata_w, these two do not match. This is clear in the following waveform, and is further rectified. [Data_inconsistency](https://github.com/shrutiprakashgupta/RISCV_Formal_Verification/blob/main/top_2/result/rdata_for_hazard_bug.png)

# Tests Passed
All of the assertions pass. The failing case i.e. memory hazard case is shown in waveform. The relevant signal file and the waveform snip is included in the folder result.
