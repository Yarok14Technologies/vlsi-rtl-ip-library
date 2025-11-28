Nice — here are **practical, high-value coding tasks** (TCL + SDC) you can do to practice and show in interviews for Physical Design / PnR / STA roles. For each task I give:

1. **What to do** (goal),
2. **Why it matters**,
3. **A compact TCL script** (Cadence Innovus / Synopsys-ish / OpenROAD where relevant), and
4. **SDC snippets** you would pair with it, plus quick verification commands.

Do them locally (OpenLane/OpenROAD for Sky130 or your commercial tools). Feel free to ask for file-specific edits or a runnable script for your environment next.

# 1. Full simple PnR flow (read netlist → floorplan → place → CTS → route → signoff)

**Goal:** Run a minimal automated PnR flow to produce routed design and signoff timing reports.
**Why:** Shows you can drive tool flow end-to-end.

**TCL (Cadence Innovus / generic):**

```tcl
# pnr_flow.tcl (Cadence-style)
set design my_top
set top_netlist ${design}.v
set liberty /path/to/libs/typ.lib
set lef_list {/path/to/tech.lef /path/to/standard_cells.lef}

# 1) setup
read_verilog $top_netlist
read_liberty -library $liberty
foreach lef $lef_list { read_lef $lef }

# 2) create floorplan
create_floorplan -core_area {0 0 1000 1000} -site core_site
set_db core_utilization 0.65
create_power_grid -rows 10 -cols 10

# 3) placement
place_opt_design -max_place_iters 5 -utilization 0.65

# 4) CTS
create_clock_tree -root_clk clk -buf_type BUFX4 -target_skew 200ps

# 5) routing
route_design -detailed

# 6) signoff
extract_rc -all
report_timing -sort_by slack -max_paths 20 > timing_postroute.rpt
report_drc > drc.rpt
write_gds final_design.gds
```

**SDC (sdc.sdc):**

```sdc
# clocks
create_clock -name clk -period 10.0 [get_ports clk]
# input/output
set_input_delay 2.0 -clock clk [get_ports {din*}]
set_output_delay 2.0 -clock clk [get_ports {dout*}]
# exceptions
set_false_path -from [get_clocks async_clk] -to [get_clocks clk]
set_multicycle_path 2 -setup -from [get_ports fast_in] -to [get_registers reg_q]
```

**Verify:** `report_timing -signoff` and inspect `timing_postroute.rpt` for negative slack.

---

# 2. Create and constrain multi-clock design (synchronous and async domains)

**Goal:** Correctly declare clocks, clock groups, false paths and multicycle paths.
**Why:** Most interview/coding tasks test multi-clock SDC knowledge.

**SDC:**

```sdc
# primary clocks
create_clock -name clk_a -period 5.0 [get_pins core/clk_a]
create_clock -name clk_b -period 10.0 [get_pins core/clk_b]

# set clock groups (no reconvergence optimism)
set_clock_groups -asynchronous -group {clk_a} -group {clk_b}

# false path from domain A to B
set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]

# multicycle example: output stable for 2 cycles
set_multicycle_path 2 -setup -from [get_cells producer/*] -to [get_cells consumer/*]
set_multicycle_path 1 -hold -from [get_cells producer/*] -to [get_cells consumer/*]
```

**TCL snippet to add SDC to flow:**

```tcl
read_sdc sdc.sdc
update_timing
report_timing -sort_by slack -max_paths 10 > multi_clock_report.rpt
```

---

# 3. Fix a setup violation using buffering / sizing (TCL automated)

**Goal:** Find worst path and insert buffer or upsizing logic to close setup.
**Why:** Demonstrates timing repair automation.

**TCL (generic / Synopsys-like):**

```tcl
# find worst path
set worst [report_timing -sort_by slack -max_paths 1 -delay_type max]
# parse the endpoint register name (tool-specific parsing; assume variable worst contains path)
# Example action: upsize cell on a net 'net_foo' (pseudo)
set_net -name net_foo
foreach inst [get_nets net_foo -drivers] {
  # upsize instance if small cell
  if {[get_cell_property $inst "cell_size"] == "X1"} {
    set_cell_property $inst "cell_size" "X4"
  }
}
opt_design -buffer_insertion
route_design -incremental
report_timing -max_paths 20 > after_fix.rpt
```

**SDC:** same clocks. After fix, `report_timing` should show reduced negative slack.

---

# 4. Design an asynchronous FIFO (RTL task) + SDC for asynchronous crossing

**Goal:** Implement async FIFO RTL, demonstrate SDC: declare false paths between clocks, and generate CDC constraints.
**Why:** FIFO + CDC is a common interview pair.

**SDC (part):**

```sdc
# clocks
create_clock -name wr_clk -period 10 [get_ports wr_clk]
create_clock -name rd_clk -period 10 [get_ports rd_clk]

# mark async domains (no timing checking across them except CDC verified)
set_clock_groups -asynchronous -group {wr_clk} -group {rd_clk}

# exclude FIFO internal pointer paths from STA (handled by CDC tool)
set_false_path -from [get_pins fifo_wr_ptr*] -to [get_pins fifo_rd_ptr*]
```

Provide RTL? (You asked for TCL+SDC; but if you want, I can give SystemVerilog FIFO RTL too.)

---

# 5. Create floorplan with memory macros and I/O pads (TCL)

**Goal:** Place macros, reserve core area, create power straps and keepouts.
**Why:** Macro placement & power planning are core PDE skills.

**TCL (Innovus-style):**

```tcl
# floorplan_macros.tcl
create_floorplan -core_area {0 0 5000 4000} -site core_site
# place memory macros
place_macro -name SRAM0 -xy {800 1200}
place_macro -name MACRO_PLL -xy {100 3500}
# create blockages
create_blockage -type hard -area {1000 0 1500 300}
# power straps
create_power_strap -layer M3 -width 2 -pitch 40
```

**SDC:** normal clocks. For memory macros, exclude internal timing if vendor provided model:

```sdc
set_false_path -from [get_cells sram0/*] -to [get_cells sram0/*]
```

---

# 6. CTS tuning: add buffer tree and skew goals (TCL + SDC)

**Goal:** Build CTS with clock buffers and set target skew / latency.
**Why:** CTS is repeatedly asked.

**TCL (CTS example):**

```tcl
# create CTS with target skew and buffer type
create_clock_tree -root_clk clk -buf_type BUFX8 -target_skew 50ps -max_fanout 128

# insert inserted_clock buffers around macros
insert_clkbuf -cells {CLKBUFX2 CLKBUFX4} -max_fanout 32
optimize_clock_tree -skew_target 50ps
```

**SDC:**

```sdc
create_clock -name clk -period 5.0 [get_ports clk]
set_clock_uncertainty 0.05 clk
set_clock_latency -source 0.2 -clock clk
```

---

# 7. Route-congestion fixing script (TCL)

**Goal:** Detect congested regions and apply cell spreading or re-route hints.
**Why:** Shows ability to debug and fix congestion programmatically.

**TCL:**

```tcl
report_congestion -all -outfile congestion.rpt
# parse congestion.rpt (tool-specific) and create blockages where congested
# pseudo: for each hotspot, create soft blockage and re-run legalize.
create_blockage -type soft -area {x1 y1 x2 y2}
opt_design -place -reoptimize
route_design -incremental
```

---

# 8. SDC advanced: false paths, multicycle, output/input delays, clock uncertainty

**Goal:** Make a robust SDC for an SoC with JTAG, async resets, multi-cycle paths (CPU), external IO.
**Why:** Interviewers want clean, correct SDCs.

**SDC (example):**

```sdc
# clocks
create_clock -name sys_clk -period 2.5 [get_ports sys_clk]
create_clock -name periph_clk -period 5.0 [get_ports periph_clk]

# I/O delays
set_input_delay -clock sys_clk 1.5 [get_ports {ext_data_in[*]}]
set_output_delay -clock sys_clk 2.0 [get_ports {ext_data_out[*]}]

# false paths (JTAG/debug)
set_false_path -from [get_ports jtag_tck] -to [get_clocks *]

# multicycle paths for CPU fetch-decode pipeline (example)
set_multicycle_path 2 -setup -from [get_registers pc_reg] -to [get_registers dec_reg]
set_multicycle_path 1 -hold -from [get_registers pc_reg] -to [get_registers dec_reg]

# exceptions: disable timing on scan chains after scan insertion
set_false_path -from [get_ports scan_in*] -to [get_ports scan_out*]
```

---

# 9. ECO insertion TCL (post-route fix)

**Goal:** Automate small ECO changes (tieoffs, buffer insertion) using TCL.
**Why:** You’ll be tested on post-route ECO in interviews.

**TCL (generic):**

```tcl
# tie-off unused inputs
foreach pin [get_ports UNUSED_*] {
  set_net -connect [create_net VSS] $pin
}

# insert buffer on net named slow_net
insert_buffer -net slow_net -cell BUFX4 -placement near {x y}
opt_design -reroute -incremental
report_timing -max_paths 10 > eco_timing.rpt
```

---

# 10. STA report automation + parsing for interview demo

**Goal:** Produce a compact timing summary, failing paths, and compare pre/post fix.
**Why:** Being able to extract metrics quickly is valuable.

**TCL:**

```tcl
# run signoff STA and produce CSV
report_timing -from [all_inputs] -to [all_outputs] -sort_by slack -max_paths 50 -format csv > timing_summary.csv
# produce slack histogram (tool-specific) or parse CSV externally with Python
```

---

## Quick checklist for running & showing results in interviews

* Always check `report_timing -signoff` (post-route) and `report_timing -delay_type max/min` for worst paths.
* Use `report_power`, `report_drc`, `report_leakage` where appropriate.
* Keep SDC & TCL in the repo; show `git diff` to demonstrate changes you made.
* Generate before/after timing reports and a 1-slide summary: worst slack, #violations, max freq reached, area/utilization.

---

## Want runnable examples for OpenLane/OpenROAD (Sky130)?

I can convert one of the above tasks (e.g., full PnR flow or CTS) into a runnable OpenLane/OpenROAD script using your Sky130 setup. Tell me **which task** and I’ll produce a ready-to-run script plus `Makefile` steps and expected outputs.

---

Would you like:

* (A) Full worked example for **Task 1** (complete tcl + sdc + expected reports), or
* (B) A runnable **OpenROAD/OpenLane** script for Sky130, or
* (C) SystemVerilog FIFO + the CDC SDC + CDC checklist?

Pick one and I’ll produce the full runnable code & comments.
