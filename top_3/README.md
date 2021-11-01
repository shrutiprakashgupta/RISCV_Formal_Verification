# Combined Verification - Execute Stage  
The testbench used is the same as that for individual execute stage. All of the assumptions except those related the instruction and data memory data values are kept - as these as quite large modules, thus it is not a good idea to keep the RTL in the test environment. 

# Errors/Bugs Detected
A bug is found in the division instruction in exceptional case, when the divisor is 0. The output is incorrect even after 32 cycles, and thus a new section of RTL is added to correct this.
```
end else if (div_request_w) begin  
    if(mul_div_b_w == 0) begin
        div_count_r <= 5'd0;
        div_busy_r  <= 1'b0;
        div_ready_r <= 1'b1;
        div_quot_r  <= 32'hffff_ffff;
        div_rem_r   <= 32'h0;
    end
    else begin
        div_count_r <= 5'd31;
        div_busy_r  <= 1'b1;
        div_quot_r  <= mul_div_a_w;
        div_rem_r   <= 32'h0;
    end
end
```
# Tests Passed
All of the assertions pass after this change is made. However, writing assertion for the division instruction took several iterations and correction steps.
