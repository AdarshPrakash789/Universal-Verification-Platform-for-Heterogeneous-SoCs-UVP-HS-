# Universal Verification Platform for Heterogeneous SoCs (UVP-HS)
### Objective:
Develop a reusable, scalable UVM-based verification environment supporting heterogeneous SoC components (ARM, RISC-V, DSPs).

### Tech Stack:
- SystemVerilog, UVM, SVA, C
- Synopsys VCS, Verdi
- Protocols: AXI, AHB

### Directory Structure:
```
uvp-hs/
├── env/
│   ├── testbench.sv
│   ├── scoreboard.sv
│   ├── coverage_collector.sv
├── agents/
│   ├── axi_agent.sv
│   └── ahb_agent.sv
├── tests/
│   ├── base_test.sv
│   └── random_test.sv
├── assertions/
│   └── protocol_assertions.sv
├── Makefile
├── compile.f
```

### Code Files

**compile.f**
```
+incdir+./env
+incdir+./agents
+incdir+./tests
+incdir+./assertions

./env/testbench.sv
./env/scoreboard.sv
./env/coverage_collector.sv
./agents/axi_agent.sv
./agents/ahb_agent.sv
./tests/base_test.sv
./tests/random_test.sv
./assertions/protocol_assertions.sv
```

**Makefile**
```
all:
	vcs -full64 -sverilog -ntb_opts uvm -debug_access+all -f compile.f -l vcs.log
	simv +UVM_TESTNAME=base_test
```

**testbench.sv**
```systemverilog
module testbench;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  initial begin
    run_test("base_test");
  end
endmodule
```

**scoreboard.sv**
```systemverilog
class scoreboard extends uvm_scoreboard;
  `uvm_component_utils(scoreboard)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", "Scoreboard running", UVM_LOW);
  endtask
endclass
```

**coverage_collector.sv**
```systemverilog
class coverage_collector extends uvm_component;
  `uvm_component_utils(coverage_collector)

  covergroup trans_cg;
    option.per_instance = 1;
    coverpoint op_type;
  endgroup

  int op_type;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    trans_cg = new();
  endfunction

  task run_phase(uvm_phase phase);
    op_type = $urandom_range(0, 3);
    trans_cg.sample();
  endtask
endclass
```

**protocol_assertions.sv**
```systemverilog
property write_followed_by_read;
  @(posedge clk) disable iff (!reset_n)
    write_valid |-> ##[1:3] read_valid;
endproperty

assert property (write_followed_by_read);
```

**base_test.sv**
```systemverilog
class base_test extends uvm_test;
  `uvm_component_utils(base_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    `uvm_info("TEST", "Running base test", UVM_MEDIUM);
  endtask
endclass
```

**axi_agent.sv**, **ahb_agent.sv** will contain complete sequencer, driver, and monitor code based on AXI/AHB protocol specs as per UVM guidelines.

### Author:
**Adarsh Prakash**  
Email: kumaradarsh663@gmail.com  
Mobile: +91 7033675921

---
