# RISC V Formal Verification

## Introduction
This repository is my first experience with full-fleged implementation of Formal Testbench. A four-stage RISC V processor supporting IM instructions is verified with [Formal verification](https://research.ibm.com/haifa/conferences/hvc2013/present/SvaFvTutorialHVC2013.pdf) technique. The tool used for exercising and covering assertions is [Jasper Gold](https://www.cadence.com/ko_KR/home/tools/system-design-and-verification/formal-and-static-verification/jasper-gold-verification-platform.html). However, this is not an open source tool, the testbench is written in [System Verilog](https://en.wikipedia.org/wiki/SystemVerilog#:~:text=SystemVerilog%2C%20standardized%20as%20IEEE%201800,test%20and%20implement%20electronic%20systems.&text=It%20is%20commonly%20used%20in,as%20an%20evolution%20of%20Verilog.) which is standard language for the EDA tools and the testbench can be modified to work with other compatible simulators. More information about the system verilog assertion syntax can be found [here](https://staging.doulos.com/knowhow/systemverilog/systemverilog-tutorials/systemverilog-assertions-tutorial/).   

## Formal Verification
The concept of writing a formal testbench was quite different from that of a direct verification testbench, as here I had to figure out the properties which should be held good by the processor across all possible cases. As the processor supports several instructions, involving branch and jump which can change the flow of control largely, finding an end-to-end property (or a statement which holds good always) was quite difficult. For ex. a simple ADD instruction can take its operands from the immediate value or register file, which can in turn have a hazard with execute or memory stage and thus the value would change on the fly. Thus, I decided to verify the individual pipeline stages separately. <br>
However, while verifying onw stage, if other stages (which are currently untested) are present in the RTL, then it will be difficult to identify if a bug is caused due to the DUT or any other stage. Thus the [assume-guarentee](http://www.cecs.uci.edu/~papers/compendium94-03/papers/2000/aspdac00/pdffiles/1c_4.pdf) technique is used. The abstracted stages are modeled with `assumptions` in the testbench, the memory blocks (instruction_memory and data_memory) are also black boxed, and the assertions on written on one block at a time. The folders `stage1`, `exe_stage`, `hazard_detect`, `mem_stage` contain these testbenches. <br>
Once this is done, then the full-RTL testing is to be done. The same testbenches are used again, but this time the assumptions are removed and the direct RTL modules are connected. So that the progress made my the processor is completely dependent on the RTL and the assertions are there to check if the proper behaviour is observed. However, the data blocks are still kept black boxed due to the large size of the memory blocks and thus the complexity involved in instantiating them. The testbenches and results for each of the stages (as a component of the whole processor) is present in `top_1`, `top_2`, `top_3` and `top_4`. 

## Design Hierarchy
```
top.sv 
defines.sv 
| -- stage1.sv 
| -- hazard_detection.sv (combinational) 
| | -- instruction_memory.sv 
| -- exe_stage.sv 
| | -- adder.sv 
| | -- shifter.sv 
| | -- multiplier.sv 
| | -- divider.sv 
| -- mem_stage.sv 
| | -- data_memory.sv 
| -- (wb_stage.sv - removed) 
| | -- register_file.sv 
```

## Errors/Bugs Detected
Several bugs including some as simple as signals defined with wire and register behaviours (while the other one was expected) to as complex as incorrect functioning of the stall signal, coming from the execute stage, to stall the PC while division operation is in progress and then resume the processing. Each of these errors (module wise) are mentioned in the respective folders (README files). <br> 
For more detailed reports, refer to the individual folders. 
