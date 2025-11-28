Nice — awesome DFT checklist. I can do any of the three options you listed. To be most useful right away, I’ll **start by giving concise, interview-ready answers for the first chunk of questions (DFT Basics → Scan Timing / Multi-clock test)** so you can see the level/detail I’ll use. If you like the style I’ll continue and finish the rest (MBIST, BIST, JTAG, ATPG, advanced, case problems) or jump straight to practical artifacts (scan FF RTL, scan insertion TCL, SDC, MBIST FSM, ATPG report, or a mock interview).

Below are compact, high-value answers you can use in interviews or expand into writeups. If you want longer explanations, diagrams, or code next, say which and I’ll produce them.

# 🟦 DFT BASICS — concise answers

**1. What is DFT and why is it needed?**
Design For Testability (DFT) are techniques added to an IC during design to make manufacturing and field testing practical, cost-effective, and with high coverage. Needed because complex SoCs have huge controllability/observability gaps, so pure functional tests miss faults; DFT enables structural fault detection, speeds up diagnostics, reduces ATE time, and improves yield.

**2. What types of testing do we do in DFT? Structural vs Functional test**

* *Structural test*: Detect manufacturing defects modeled as faults (stuck-at, delay, bridging). Uses ATPG, scan, BIST.
* *Functional test*: Exercising functional vectors — catches logical bugs and some defects but is generally lower defect-detection efficiency and slower for mass test.

**3. Difference between fault simulation and functional simulation**

* *Fault simulation*: Simulates models of physical defects (e.g., stuck-at) under test patterns to compute fault coverage. Uses a good fault list and compaction techniques.
* *Functional simulation*: Simulates RTL/netlist with stimulus to verify logical correctness — not designed to measure manufacturing-defect detectability.

**4. What is fault coverage? Types?**
Fault coverage = fraction of targeted fault list detected by a given test set. Types: single-fault coverage (stuck-at), transition/delay coverage, path delay coverage, IDDQ coverage, bridging-fault coverage, pattern-dependent coverage (power/capture). Also structural vs behavioral coverage distinctions.

**5. What is ATPG? What’s the goal?**
Automatic Test Pattern Generation — tool/algorithm to produce patterns that detect modeled faults. Goal: maximize fault coverage while minimizing pattern count, test application time, and power during capture.

**6. Fault models (stuck-at, transition, IDDQ, bridging, stuck-open)**

* *Stuck-at*: Node permanently 0/1 — classical gate-level model.
* *Transition (stuck-transition)*: Used for delay faults (slow-to-rise/fall).
* *IDDQ*: Quiescent current testing to detect leakage-inducing defects.
* *Bridging*: Two nets shorted — can be modeled as dominant/driven; challenging for ATPG.
* *Stuck-open*: Pass transistor/open causing floating behavior — needs special test/initialization strategies.

**7. Observability and controllability**

* *Controllability*: Ease of setting a node to 0/1 from primary inputs/scan.
* *Observability*: Ease of observing a node’s value at primary outputs/scan out. DFT techniques (scan test points, boundary scan) increase both.

**8. What is a test point? Why insert it?**
Test point = added logic (control or observation) to improve controllability/observability of internal nodes for ATPG. Inserted when fault coverage low or for timing/clock domain debug. Types: control TP (force node value), observation TP (route internal node to a scan/PO).

---

# 🟩 SCAN DESIGN — concise answers

**9. Why do we add scan?**
Scan converts sequential elements into a shift-chain for deterministic controllability/observability of sequential state, enabling combinational ATPG to effectively test sequential circuits and reach high structural coverage.

**10. MUXed scan flip-flop — structure + timing**
A muxed-scan FF adds a 2:1 mux before D: one input from functional D, other from scan shift-in. Scan_enable selects shift path. Timing: extra mux adds combinational delay to D -> Q (capture path) and insertion affects setup; SED (scan enable) gating and hold during shift are critical.

**11. What is a scan chain? How does it operate?**
A serial chain of scan FFs (or multiple chains) where during *shift* mode you serially load and unload test vectors (scan-in/scan-out). During *capture* you apply functional clocks to capture responses. Modes: shift, capture, and sometimes preprocess/postprocess.

**12. Scan-in, scan-out, capture, shift — short**

* *Scan-in/out*: Serially shift test vector into/out of chain during shift cycles.
* *Shift*: Repeated clock pulses with scan_enable active for serial load/unload.
* *Capture*: Switch to functional mode and apply one/two clocks to capture the circuit response into scan cells.

**13. Internal scan vs boundary scan**

* *Internal scan*: On-chip scan chains that expose internal FFs to ATPG. Used for manufacturing stuck-at/delay tests.
* *Boundary scan (IEEE 1149.1)*: Flip-flops at chip IO to test board-level interconnects, allow EXTEST/INTEST etc. Focuses on board test and in-circuit visibility.

**14. How do you partition scan chains?**
Partition by balancing chain lengths (shift time), physical placement to minimize routing, clock domain (keep same clock domain), power domains, test compression strategy, and ATE port constraints. Also consider yield and ECO constraints.

**15. What happens if scan_enable toggles during shift mode?**
If scan_enable toggles, you can corrupt the shifted pattern, create metastability or mixed-mode capture, and cause X propagation. It breaks deterministic loading — ATPG patterns assume stable SE during shift. Tools/constraints require SE stable; ensure SE domain synchronous and glitch-free.

**16. What is scan chain reordering? Why?**
Reordering changes the physical order of FFs in chains (without changing functional connectivity) to reduce routing congestion, balance chain lengths, or improve test compression and timing. Done in PNR with scan-chain-aware placement.

**17. Issues due to long scan chains?**

* Long shift time → higher test cost.
* Increased shift power and IR-drop during shift.
* Timing/hold problems in shift domain.
* Single chain failure kills visibility for many FFs — reduce by multiple chains.

**18. What is lock-up latch? Where & why used?**
A lock-up latch (or hold latch) is used to capture data around clock gating when clocks are disabled — avoids combinational glitching or to break timing cycles when gating removes the clock. In test, used to maintain state during power/clock management transitions.

**19. What causes X-propagation in scan and how to fix it?**
X-propagation from uninitialized memories, tristates, asynchronous resets, or crosstalk can drive unknowns into scan chains. Fixes: initialize RAMs/registers, use X-fill/drive circuits, force safe values via control TPs, apply ATPG X-sensing, and ensure proper reset sequencing. Use masking/compaction solutions for X in signatures.

---

# 🟧 SCAN TIMING & MULTI-CLOCK TEST — concise answers

**20. What is scan shift timing mode?**
A timing mode where flip-flops are clocked repeatedly with scan_enable active; timing paths differ (shift clocks are usually slower). Shift-clock timing constraints and hold checks are critical because different clock trees and gating may apply.

**21. Why is hold critical in shift mode?**
During shift, the scan clock toggles frequently and data shifts through adjacent FFs — insufficient hold time causes data overwrite or corruption. Since shift clocks can be fast and routing paths short, hold violations are frequent and require careful constraints or insertion of hold fixes (buffers, hold-FFs).

**22. Why is setup more critical in capture mode?**
Capture mode uses functional clocks and is where ATPG tests are launched and captured; setup ensures correct sampling of DUT response. Fault detection depends on reliable capture sampling — setup failures here cause false fails or missed faults.

**23. How do you handle scan chains across different clocks?**
Prefer to group scan cells by clock domain into separate chains, or add synchronizers for SE and shift clocks. Solutions: domain-specific chains, use multi-domain scan insertion (one chain per clock), use boundary cells at CDC points, ensure SE domain crossing is safe and constant during shift.

**24. What is test clock gating bypass?**
A mechanism to bypass gating during test so clocks required by scan/ATPG are visible and functional; typically test mode forces clock enables to open. Ensures gated clocks don’t block scan or capture operation. Controlled via test mode signals in clock-gating cells.

**25. What constraints are required in test mode?**
Typical SDC: set_test_mode true, declare scan clocks and shift/capture clocks, set false paths across scan muxes or scan enable pins, set_disable_timing or false_path for SE signals, and ensure proper IO/clock gating checks. Example lines were shown in your SDC snippet.

---

If this level works for you I’ll continue and cover:

* MBIST/Mem test (March tests, repair, BISR)
* LBIST basics, LFSR/MISR, aliasing & power reduction
* JTAG/1149.x details
* ATPG/compression (EDT, X-compactors, LOC/LOS)
* Advanced DFT (power gating, chiplets, IJTAG)
* Case-based problem answers
* AND/OR produce the practical artifacts (scan-FF RTL, scan insertion TCL, SDC, ATPG report example, MBIST SV FSM) and a mock interview.

Which should I do next?
A — Finish all QA answers now (complete handbook)
B — Produce practical coding artifacts (scan FF RTL + scan insertion TCL + SDC + ATPG example)
C — Build a combined DFT + PDE + RTL mock interview set (45-minute simulation + answers + grading rubric)

Or I can continue straight through and finish the remaining Qs (MBIST → Advanced → Cases) without you choosing. What do you want me to produce *right now*?


Perfect — continuing exactly from **Q26 → Q65** with the same **concise interview-grade** format.
(You already have Q1–Q25 above.)

---

# 🟥 MBIST / MEMORY TESTING (Q26–Q32)

**26. Why can’t you just use scan for embedded memories?**
Memories are dense cell arrays without scan flops → internal nodes not directly controllable/observable → massive area/timing overhead if replaced by scan → so dedicated MBIST needed.

**27. MBIST architecture — main blocks**

* **Address generator** (up/down/random)
* **Data/background pattern generator**
* **March algorithm controller**
* **Comparator** (read compare)
* **BISR fuse/repair logic** (optional)
* **Interface to memory wrapper** (write enable, chip enable)

**28. Common Memory March algorithms**

* **March C−** (most common: detects stuck-at, transition, coupling)
* **March LR** (Left–Right, covers decoder faults)
* **March B** (higher coverage, more cycles)

**29. What are repair schemes?**
Mapping faulty memory rows/columns to **spare rows/columns** → improves yield.

**30. What is BISR?**
**Built-In Self-Repair**: Automatic detection (via MBIST) + repair using fuse map programming to remap faulty locations.

**31. Explain redundancy (spare rows/columns)**
Extra rows/columns built into RAM. On failures, fuse-based address redirection routes access to spare instead of bad cell.

**32. ECC vs BISR — which is better?**

* **ECC** = Corrects soft errors (alpha particle hits, noise) at runtime
* **BISR** = Repairs manufacturing defects permanently
  Often **both** used in high-reliability SoCs.

---

# 🟪 LOGIC BIST (LBIST) (Q33–Q37)

**33. What is LBIST? When is it used?**
On-chip pseudo-random test pattern generation (LFSR) + response compaction (MISR).
Used in automotive, aerospace, servers → **in-field periodic self-test**, safety compliance (ASIL, ISO-26262).

**34. What is LFSR? What is MISR?**

* **LFSR**: Linear feedback shift register → generates pseudo-random stimuli
* **MISR**: Multiple-input signature register → compresses responses into signature

**35. What is signature analysis?**
Final MISR value = **signature**. Compare with expected (golden) signature → if mismatch = fail.

**36. What is aliasing in LBIST? How minimized?**
Different fault responses produce same MISR signature.
Reduce by:

* Using primitive-polynomial LFSR/MISR
* Larger MISR width
* Pattern count increase

**37. Power issues in LBIST — how reduced?**
Random patterns toggle too many nets → IR drop.
Fixes: weighted pseudo-random patterns, clock gating, phase shifters, low-power X-fill, reduce shift frequency.

---

# 🟫 JTAG / IEEE 1149.1 (Q38–Q42)

**38. Why do we need boundary scan?**
To test board-level interconnect faults (opens/shorts) **without probes**.

**39. Explain TAP controller state machine**
16-state FSM controlling scan path:
**Test-Logic-Reset → Run-Test → DR states → IR states**
Transitions controlled by **TMS** on **TCK**.

**40. EXTEST vs INTEST vs BYPASS**

* **EXTEST**: Test board traces between chips
* **INTEST**: Test internal logic via boundary cells
* **BYPASS**: Skip the chip to shorten chain

**41. Difference between 1149.1 and 1149.6**
1149.6 supports high-speed differential IO testing (AC-coupled nets).

**42. How is JTAG used for board testing?**
Chain several ICs → shift patterns through → detect soldering defects, shorts/opens.

---

# 🔷 ATPG & FAULT COVERAGE (Q43–Q49)

**43. What is test compression and why needed?**
Reduces scan-in/out volume → fewer patterns → lower test time/cost.
Using **decompressors (EDT)** + **compactors (X-compactor)** inside chip.

**44. What are EDT and X-compactors?**

* **EDT**: Embedded Deterministic Test decompressor → expands small tester pattern to wide scan chain stimuli
* **X-compactor**: Compresses scan-out while handling unknowns (X-masking/canceling)

**45. What is capture power and how reduced?**
High toggling during at-speed capture → IR drop → false fails.
Reduce by: low-power ATPG, segment capture, clock staggering, power-aware fill, gated FFs.

**46. Launch-on-Capture (LOC) vs Launch-on-Shift (LOS)**

* **LOC**: Launch occurs during functional capture clock
* **LOS**: Launch directly from last shift → more coverage but harder timing (shift path = functional path)

**47. Why can LOS detect more faults?**
Allows **robust transition launch** on more internal nodes → tests more delay paths.

**48. Reasons for low fault coverage**

* Uncontrollable/Unobservable nodes
* Uninitialized RAMs, black box logic
* Clock gating without bypass
* Asynchronous logic / CDC
* Low-quality scan insertion

**49. How to improve coverage w/o RTL changes**

* Insert Test Points
* Enable test compression
* Handle X sources better
* Split/rebalance scan chains
* Fix DFT rule violations (e.g., bypass gating)

---

# 🔶 PHYSICAL DFT + TIMING (Q50–Q54)

**50. Scan chain constraints during PnR**

* Location-aware chain stitching
* Same clock domain grouping
* Minimize long routing
* Avoid crossing voltage/power domains

**51. Why is hold fixing critical in scan mode?**
Shift path is very short → hold fails common → buffer insertion or scan reordering needed.

**52. Power constraints impacting testing**
During shift/capture → huge simultaneous toggling → IR drop, overheating.
Use low-power X-fill, slow shift clocks, domain-wise test.

**53. SCANcell vs Non-scan cell rules**
Every sequential element must be scannable except special cases (RAM flops, analog blocks).
Ensure **consistent scan enables** and no latches in logic path unless designed for scan.

**54. DFT checks at RTL / Netlist / GLS**

| Stage          | Focus                                                      |
| -------------- | ---------------------------------------------------------- |
| RTL            | DFT rule checks, clock gating test mode logic              |
| Netlist        | Scan connectivity, test mode timing, compression structure |
| Gate Sim (GLS) | Pattern validation, X-propagation, real delays             |

---

# 🚀 ADVANCED DFT (Q55–Q60)

**55. Hierarchical DFT in chiplets**
Test wrappers per die/IP → local ATPG → compressed test data → top-level interconnect test using **die-to-die boundary scan**.

**56. DFT in power-gated designs**
Need **test power controller** to wake one island at a time, isolate shut-down domains, and route scan around powered-off logic.

**57. DFT challenges in CDC logic**
Clock domains require isolation; SE path must be synchronous. Add boundary cells, lock-up flops, domain-wise scan.

**58. IEEE 1687 (IJTAG)**
Standard for **in-chip embedded instruments** access network (sensors, monitors) using reconfigurable scan paths.

**59. How partial scan impacts ATPG**
Leaves some sequential elements un-scanned → lower coverage, harder algorithms, more patterns → used when area/power tight.

**60. Compression ratio impacts**

| Higher Compression | Effect                                 |
| ------------------ | -------------------------------------- |
| ↑ Ratio            | ↓ Patterns, ↓ ATE time                 |
| Too high           | ATPG runtime ↑, aliasing ↑, coverage ↓ |

---

# 🧠 CASE-BASED PRACTICALS (Q61–Q65)

**61. Scan chain fails in GLS — what checks?**

* Scan order mismatch vs ATPG definition
* SE glitching
* Floating reset values → Xs
* Wrong clock/phase usage
* Incomplete stitching

**62. Low transition coverage — root cause?**

* Insufficient at-speed clocks
* Clock gating not bypassed
* LOS disabled
* Reconvergent fan-out masking transitions

**63. Setup clean, hold fail in shift — why?**
Shift mode path shorter → hold violations even if capture ok → fix by reordering / buffers.

**64. Clock gating blocks scan — what to do?**
Force gating enable high in **test mode** or use integrated clock gating cells with **test override** pins.

**65. Testbench mismatch in gate sim — likely root cause?**
X-propagation, async resets not synchronized, incorrect SE during capture, uninitialized memories, wrong scan IO connection.

---



