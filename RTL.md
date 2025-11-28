Great — here are concise, interview-ready answers for **every question** you listed. I kept each answer short (2–5 lines) so you can scan and memorize quickly. Use these as oral answers in interviews — I can expand any item on request.

# 🟦 BASIC RTL QUESTIONS (Conceptual)

1. **Blocking vs non-blocking assignments**

   * Blocking (`=`) executes immediately and in sequence inside a procedural block — good for combinational modeling.
   * Non-blocking (`<=`) schedules the update at the end of the time-step — required for registering behavior to avoid race conditions in clocked logic.

2. **When to use `=` vs `<=` in SystemVerilog**

   * Use `=` for combinational logic (inside `always_comb`) and temporary vars. Use `<=` for sequential (clocked) registers inside `always_ff` to model real flip-flop updates.

3. **Combinational vs sequential logic**

   * Combinational: outputs depend only on current inputs (no state). Use gates, `always_comb`, no clock.
   * Sequential: outputs depend on current inputs and past state (flip-flops), driven by clocks or resets.

4. **How do you infer a latch unintentionally?**

   * Missing assignments on some branches in combinational blocks (e.g., not assigning an output in every `if`/`case`) causes synthesis to infer latches. Ensure full assignments or use `always_comb`.

5. **Why `always_comb` for combinational blocks?**

   * `always_comb` automatically infers sensitivity list, checks for inferred latches, and models combinational semantics; safer and more synthesizable than manual `always @(*)`.

6. **Explain setup and hold times**

   * Setup: data must be stable for some time **before** clock edge. Hold: data must be stable for some time **after** clock edge. Violations cause metastability or incorrect capture.

7. **What is metastability and how to avoid it?**

   * Metastability: flip-flop output hangs in undefined region after violating setup/hold (e.g., asynchronous input). Avoid with synchronizers, proper timing, and design margins.

8. **What is a synchronizer? Why 2-stage?**

   * A synchronizer chains flip-flops to absorb metastability and reduce probability of failure. Two stages balance latency and extremely low mean time between failures (MTBF).

9. **Mealy vs Moore FSMs**

   * Mealy: outputs depend on state + inputs (fewer states, faster reaction). Moore: outputs depend only on state (simpler timing, glitch-free outputs on state changes).

10. **Sticky/edge-detect pulse generation**

    * Edge detect: store previous input in a register and `pulse = input & ~prev_input` (rising). Sticky: latch a pulse until explicitly cleared (use set/clear registers).

# 🟩 INTERMEDIATE RTL QUESTIONS

11. **Avoiding race conditions in RTL**

    * Use non-blocking assignments for sequential logic, avoid mixing blocking/non-blocking in same clocked block, and structure code using `always_ff`/`always_comb`.

12. **Why reset synchronizers are needed**

    * Asynchronous reset deassertion can violate timing across domains; synchronizing reset deassertion avoids metastability and inconsistent release ordering across flops.

13. **Asynchronous vs synchronous resets**

    * Asynchronous: immediate effect on flops regardless of clock (fast response, potential release issues). Synchronous: reset sampled by clock (clean release, easier timing).

14. **Clock gating — what and how in RTL**

    * Clock gating saves dynamic power by disabling clock to idle registers. In RTL prefer enable-based gating (use clock enables) and let synthesis insert gating cells — avoid driven gated clocks in RTL.

15. **Priority encoder vs one-hot encoder (coding)**

    * Priority encoder: take a vector and output index of highest-priority set bit (use `for` loop or `priority` logic). One-hot encoder: convert index to one-hot with a shift or `1 << index`.

16. **Purpose of `unique case` and `priority case`**

    * `unique` tells tools that cases are mutually exclusive (enables better optimizations and safety checks). `priority` explicitly gives priority to the first matching branch, useful when overlaps are expected.

17. **Pipeline stages & why pipelining increases throughput**

    * Split combinational work into stages separated by registers; reduces critical path so clock frequency increases; throughput increases because multiple transactions are in-flight concurrently.

18. **CDC issues and fixes**

    * Cross-Domain problems: metastability, data corruption, ordering. Fixes: synchronizers for single-bit signals, FIFOs/handshakes for multi-bit paths, CDC checks, and constraints for formal tools.

19. **Multi-cycle path (MCP) — what & coding**

    * MCP: path that takes multiple cycles to be valid. Declare via SDC (`set_multicycle_path`) or encode in RTL by registering intermediate stages; ensure timing constraints reflect cycles.

20. **Retiming in synthesis**

    * Retiming moves registers across combinational logic to balance paths and optimize timing. RTL styles with complex state or gated clocks may prevent retiming.

# 🟧 ADVANCED RTL QUESTIONS

21. **Designing a parameterized AXI slave**

    * Make address/data widths, ID width, burst support, and FIFO depths parameters. Modularize channels (AW, W, B, AR, R) and use handshake-valid/ready, burst counters, and response logic with parameterized alignment.

22. **AXI handshake (VALID & READY)**

    * VALID asserted by sender when data is available; READY asserted by receiver when can accept. Transfer occurs when both are high on same cycle; either side can stall by deasserting their signal.

23. **If VALID=1 but READY=0 for multiple cycles**

    * Sender must hold data and keep VALID asserted until READY is asserted; the transfer waits (backpressure), so buffers/skid-buffers are needed to avoid data loss.

24. **Implementing AXI burst support**

    * Implement burst counters, address incrementing/wrapping logic per burst type (INCR, FIXED, WRAP), manage beat counts, handle misaligned addresses, and track outstanding transactions.

25. **Skid buffer in AXI**

    * Small FIFO placed before a core to absorb temporary backpressure when READY can’t be sampled; prevents data loss on cycle where READY falls after VALID asserted; typically one-cycle buffer.

26. **Ensuring timing closure at RTL stage**

    * Keep critical paths small, pipeline heavy combinational logic, use register balancing, synth-friendly coding, constrain clocks early, and run static timing/CDC checks frequently.

27. **Structuring large RTL into modular blocks**

    * Use hierarchy: clear interfaces, parameterization, transactions/packets, small focused modules, and well-defined buses; apply consistent naming and layer behavioral vs cycle-accurate modules.

28. **Register duplication and why synthesis does it**

    * Synthesis duplicates registers to reduce routing congestion and critical fanout or to satisfy different timing paths; improves timing at cost of area.

29. **UPF low-power concepts**

    * Isolation: block signals to powered-down domain; retention: save state to retention flops; power gating: cut off power to blocks — control states defined in UPF to enforce these on implementation.

30. **FIFO design (full/empty, Gray pointers, sync vs async)**

    * Full/empty: compare write and read pointers with proper handling of wrap (use MSB as toggle). Gray code pointers minimize bit flips across clock domains. Sync FIFO: single clock; Async FIFO: dual-clock with pointer synchronization and Gray-code to avoid metastability.

# 🟥 COMMON CODING QUESTIONS — short approach & key constructs

For each, I give the minimal synthesizable approach and key hints.

1. **Positive edge detector**

   * `prev <= sig; posedge = sig & ~prev;` inside `always_ff @(posedge clk)`. Use a one-cycle pulse register.

2. **Gray code counter**

   * Binary counter `b`; `gray = b ^ (b >> 1)`. For n-bit, update binary and compute gray for output.

3. **Asynchronous FIFO**

   * Dual-clock memory, write pointer in write domain, read pointer in read domain. Use Gray-coded pointers and synchronize opposite-domain pointers. Handle full/empty with MSB toggle comparison.

4. **Parameterized N-bit adder**

   * `module adder #(parameter N = 32) (input logic [N-1:0] a,b, output logic [N:0] sum); assign sum = a + b; endmodule` — use generate if you want ripple/carry-save options.

5. **Sequence detector 1011 (overlap & non-overlap)**

   * FSM approach: Mealy or Moore with 4 states. Overlapping: on detection, transition to state representing partial match (e.g., last bit `1`); non-overlap: reset to idle after match.

6. **One-hot FSM for traffic light**

   * Encode states one-hot, clocked state regs, next-state logic combinational. One-hot simplifies next-state decoding and timing; good for FPGAs.

7. **AXI handshaking logic**

   * For each channel: `if (valid && ready) { transfer }`. Keep internal FIFOs, backpressure, track beat counts for bursts, and assert responses when appropriate.

8. **Round-robin arbiter**

   * Maintain pointer to last grant; mask requests below pointer, grant first set bit; update pointer to next request after grant. Use fairness by rotating priority.

9. **LRU cache replacement logic**

   * For small associativity: maintain age counters per way, update on hits (set selected way age=0, increment others). For hardware, use binary tree or stack-based approximations for speed.

10. **Pipelined multiplier (with registers)**

    * Break multiplier into partial-product generation, accumulate stages with adders and registers between stages. Insert pipeline registers at boundaries to meet timing; ensure control/valid signals are pipelined too.

# 🔥 NVIDIA / QUALCOMM LEVEL QUESTIONS

1. **Detect combinational loops**

   * Use lint/graph tools to detect cycles in netlist; in RTL avoid combinational outputs fed back through combinational logic without registers; simulation X-propagation and static checks help find loops.

2. **Debug X-propagation**

   * Trace source of X using waveform, inject known values, add assertions/checks to find which signal produces X, use `xprop` reporting in simulator and eliminate uninitialized regs or multipart driver conflicts.

3. **Reduce dynamic power in RTL**

   * Clock gating (use enables), operand gating, reduce switching by flattening logic, minimize toggling of high-fanout nets, restructure algorithms to reduce activity and use lower toggle encodings.

4. **Design a 4-stage pipeline without hazards**

   * Insert forwarding paths and hazard detection unit for data hazards, branch prediction or stall/br flush mechanisms for control hazards, and ensure register stages isolate combinational logic.

5. **Branch prediction types**

   * Static (always taken/not), dynamic (BHT, 2-bit saturating counters), tournament predictors, and global/local history schemes — hardware stores history to predict direction.

6. **Out-of-Order execution scoreboard**

   * Track instruction status, register renaming, issue when operands ready, retire in-order; scoreboard maintains functional unit availability, wakeup/select logic, and commit logic.

7. **MESI coherence**

   * States: Modified, Exclusive, Shared, Invalid. Protocol ensures that caches coordinate via bus or network messages to maintain memory consistency and manage ownership.

8. **TLB and cache interaction**

   * TLB translates virtual to physical addresses before cache lookup (virt-to-phys). For physically indexed caches, translation happens first; for virtually indexed caches you must handle synonyms/aliasing.

9. **Design a non-blocking cache**

   * Allow multiple outstanding misses via Miss Status Holding Registers (MSHRs) to track pending requests and merge duplicates. Requires reordering logic and ARB for responses.

10. **N-way set associative cache indexing**

    * Index bits (from address) select set, tag compare across ways in set. Replacement uses LRU or approximations; alignment logic for block offsets and address decoding performs load/store alignment.

# 🟪 SYNTHESIS + STA QUESTIONS

1. **LINT vs CDC checks**

   * Lint: coding/style checks (combinational loops, unconnected signals). CDC: cross-clock-domain checks for safe data transfer (synchronizers, FIFOs).

2. **Retiming and RTL styles preventing it**

   * Retiming relocates registers for timing. Asynchronous resets, gated clocks, or explicit register groups / blackboxes may prevent retiming.

3. **How false paths impact timing**

   * False paths are excluded from timing analysis; incorrectly marking paths as false can hide real violations; correctly defined false paths help STA focus on real critical paths.

4. **Fixing setup violations**

   * Reduce combinational delay (pipeline), balance path (register insertion), reduce logic depth, re-synthesize with faster cells, or relax constraints (rarely).

5. **Fixing hold violations**

   * Add small delay (register buffering or routing constraints), add retiming registers, or apply hold-restoring buffers; ensure not to break functional behavior.

6. **Why avoid gated clocks in RTL**

   * Gated clocks hamper timing analysis and create clock-domain issues; prefer clock enables and let synthesis insert safe gating cells.

7. **Cause of high fanout**

   * Driving many registers or logic from a single net (e.g., reset or clock wrongly routed as combinational net) — fix by inserting buffers or distributing via register replication.

8. **Writing SDC for multi-clock domain**

   * Define clocks precisely, set clock groups for unrelated clocks, synthe constraints for generated clocks, define false paths and multicycle paths where appropriate, and set max/min delays.

9. **What are multi-cycle constraints**

   * Constraints that inform STA a path needs N cycles to resolve; used for intentionally longer paths (e.g., multi-cycle datapaths) and avoid false violations.

10. **Why register balancing is needed**

    * Evenly distribute registers to equalize path delays and reduce critical path lengths — improves timing and helps retiming/synthesis.

# 🟦 UVM + VERIFICATION QUESTIONS FOR RTL ENGINEERS

1. **What is a scoreboard?**

   * A verification component that checks DUT outputs against expected reference model, typically comparing transactions and flagging mismatches.

2. **What is a virtual interface?**

   * A SystemVerilog construct allowing testbench components to access DUT signals through an abstract handle—used for connecting drivers/monitors to RTL interfaces.

3. **Functional coverage vs code coverage**

   * Functional coverage measures verification completeness of functional scenarios/state space; code coverage measures exercised RTL code lines/branches. Both are complementary.

4. **Explain UVM phases**

   * UVM phases: build, connect, end_of_elaboration, start_of_simulation, run_phase, extract/report — coordinate component lifecycle and simulation sequencing.

5. **How do you debug simulation mismatches?**

   * Reproduce minimal failing test, enable waveforms, add assertions/prints, cross-check scoreboard and reference model, bisect stimulus to find root cause.

6. **What is SVA (SystemVerilog Assertions)?**

   * Property language to assert temporal behaviors (immediate and concurrent assertions), used for formal checks and simulation-time verification.

7. **Property: `req` must be followed by `ack` within 3 cycles**

   * Example SVA: `property p_req_ack; @(posedge clk) req |-> ##[1:3] ack; endproperty; assert property (p_req_ack);` (adjust reset conditioning).

8. **Constrained random vs directed tests**

   * Directed tests target specific corner-cases; constrained random tests sample broad stimulus space within constraints to find unexpected bugs and improve coverage.

9. **Monitor vs driver**

   * Driver applies stimulus to DUT (driving signals). Monitor passively observes DUT signals, converts to transactions, and forwards to scoreboard/coverage.

10. **What is a transaction-level model (TLM)?**

    * Abstract representation of data/operations (transactions) decoupled from pin-level signaling; used in UVM/TLM for high-level stimulus and faster simulation.

---


Which one should I generate now — (code for a specific problem), (detailed writeup for a difficult question), or (PDF cheat sheet)?
