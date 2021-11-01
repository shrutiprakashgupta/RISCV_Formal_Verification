# Top Module
This directory was set up at the beginning of the verification of complete design (integrated). Before this, the individual blocks have been verified and the following changes are made - introduction of stall signal from execute stage while division operation is in progress, write back stage removed due to its extra delay addition and not-so-useful functionality and, several other debugging changes. Here, the aim is to integrate all modules having updated RTL and ensure proper and functional hierarchy. This is the reason that no other signal is put on the interface except the clk and rst. However, while writing the testbench, more signals will be added to the interface for probing. <br>
> Note: While write back stage is removed, the 4-cycle pipeline is maintained, as the register file is clocked, so it takes one cycle to write the value to a specific register location. The write back stage originally available with the code was just a wrapper module (which forwarded the signals to the register file). Also, the register file being a direct RAM logic with relatively small size of 32 registers, doesn't need formal verification.

# Hierarchy
```
top.sv <br>
defines.sv <br>
| -- stage1.sv <br>
| -- hazard_detection.sv (combinational) <br>
| | -- instruction_memory.sv <br>
| -- exe_stage.sv <br>
| | -- adder.sv <br>
| | -- shifter.sv <br>
| | -- multiplier.sv <br>
| | -- divider.sv <br>
| -- mem_stage.sv <br>
| | -- data_memory.sv <br>
| -- (wb_stage.sv - removed) <br>
| | -- register_file.sv <br>
```

# Testbench Hierarchy
```
tb_top.tcl <br>
| -- bind_top.sv <br>
| | -- tb_top.sv <br>
| | -- defines.sv <br>
| | -- top.sv <br>
| | ... same hierarchy as defined above
```

# Verification Plan
## Progress Till Now
1. The individual blocks are verified.
2. For the verification of modules (stage1, hazard_detection, exe_stage and mem_stage), the rest of the modules are abstracted - modeled by constraining the random input injected by the tool (Jasper Gold) and the original RTL is removed. 
3. The larger (in terms of data size) and lesser complex modules - like the instruction_memory and data_memory are black boxed. The instruction_memory is captured in the assumptions and the data_memory interface is randomized in terms of data, and the control logic is verified. 

## Verification of Combined modules
1. Given the modules are cascaded in the pipeline, the verification of individual modules should be sufficient, given the model of all abstracted or black boxed modules is correct.
2. To validate the assumptions written to model the modules, the same testbench (used for individual modules) is used over the combined design and all of the assumptions are removed. This leaves the processor free to evolve in all possible paths, and yet the assertions should hold good. 
3. This is the verification plan currently being followed. 
