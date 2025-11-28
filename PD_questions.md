# Full answers for all **95 Physical Design (PDE)** interview questions

Below are concise, interview-ready answers (one short paragraph each) followed by 3–5 bullet points: **what the hiring manager is listening for**. Use these as talking points — short, precise, and practical.

---

## 🟦 BASIC PHYSICAL DESIGN (PnR) QUESTIONS

### 1. What are the steps in a typical **physical design flow**?

**Answer:** Typical flow: RTL → Synthesis (netlist, constraints) → Floorplanning (die/cell/macros, core utilization, power rings) → Power planning (power grid, straps, floors) → Placement (standard cells, macros) → Clock Tree Synthesis (CTS) → Routing (global → detailed) → ECO/Timing fixes → RC extraction → STA → DRC/LVS/Signoff checks → Tapeout. Iterations happen between placement/CTS/routing/STA until timing, power, and DRCs are clean.
**Hiring manager listening for:**

* Knowledge of iteration loop and where STA/DRC fit.
* Awareness of power/clock steps and extraction before signoff.
* Ability to mention tools/artefacts (netlist, SDC, GDSII).

### 2. Explain **core utilization**.

**Answer:** Core utilization = ratio of utilized cell area to available core area (excluding I/O/pads). High utilization reduces die size but can increase congestion and routing difficulty; low utilization wastes area and can hurt density/power. Typical targets vary by design/macro density (e.g., 60–80%), tuned per floorplan constraints.
**Hiring manager listening for:**

* Trade-offs: density vs. routability.
* Familiarity with target ranges and adjusting utilization locally.
* Strategies like whitespace distribution and channel planning.

### 3. What is the difference between **core area** and **die area**?

**Answer:** Core area refers to the internally usable silicon region for logic/macros (excluding IO/pads and passive areas). Die area is the total silicon area including core, I/O rings, scribe lines, and any keep-out regions — it determines cost and yield.
**Hiring manager listening for:**

* Cost/yield implications of die size.
* Distinction for floorplan decisions (placing macros vs IO).
* Awareness of scribe and assembly considerations.

### 4. What is **aspect ratio** in floorplanning?

**Answer:** Aspect ratio = width-to-height ratio of the core (or a block). It affects routing resources, power grid topology, and timing. Choosing an aspect ratio balances die shape constraints, IO pitch, macro orientation, and manufacturability.
**Hiring manager listening for:**

* How aspect ratio affects wirelength/skew.
* Practical trade-offs (narrow tall vs. wide shallow).
* Examples of when you'd change it.

### 5. What is a **macro** and a **soft block**?

**Answer:** A macro is a pre-designed, often fixed-layout hard block (memory, PLL, I/O, SERDES) with fixed placement and routing requirements. A soft block is a synthesized block provided as RTL or leaf-level netlist that can be placed and routed like standard cells (e.g., synthesized IP).
**Hiring manager listening for:**

* Hard vs soft trade-offs (fixed pins, power rails).
* Handling macro routing/pin-access and power straps.
* Experience with memory macros and their special needs.

### 6. Why do we need **tap cells** and **endcap cells**?

**Answer:** Tap cells connect substrate/wells to power rails to ensure proper well biasing and prevent latch-up. Endcaps close standard cell rows to maintain continuity for rails and DRC rules. They are required to meet process rules and ensure robust well ties.
**Hiring manager listening for:**

* Role of substrate ties in analog/digital separation.
* DRC reasons and placement conventions.
* Impact on standard cell row planning.

### 7. What are **tie-high** and **tie-low** cells?

**Answer:** Tie-high (VDD) and tie-low (VSS) cells provide constant logic '1' and '0' outputs used to tie unused inputs or implement constant nets. They prevent floating nets and are placed with care to avoid routing congestion and timing issues.
**Hiring manager listening for:**

* Why floating inputs are bad.
* Placement and power considerations.
* Use cases (tie-off reset polarity, constant generation).

### 8. Difference between **pre-CTS** and **post-CTS** optimization.

**Answer:** Pre-CTS optimizations adjust placement, buffering, net restructuring, and path restructuring to reduce skew/latency before clock tree creation. Post-CTS optimizations focus on routing-driven fixes, buffer insertion, re-sizing, and CTS ECOs after clock tree and initial routing have been built, often to fix violations discovered by post-route STA.
**Hiring manager listening for:**

* Examples of pre-CTS steps (useful skew, buffer insertion).
* Post-CTS fixes (clock gating, deskew buffers, hold fixes).
* Trade-offs and risks when changing placement post-CTS.

### 9. Why is routing done in multiple layers?

**Answer:** Multiple metal layers provide routing capacity, separate vertical and horizontal routing directions, allow faster low-resistance upper metals for long runs, and distribute power/ground. Layer stacking is optimized for pitch, resistance, capacitance, and via patterns.
**Hiring manager listening for:**

* Relationship between layer and RC/timing.
* Typical direction assignment and upper-layer use for global nets.
* Via planning and layer transitions.

### 10. What is **congestion** and how do you reduce it?

**Answer:** Congestion is local over-subscription of routing resources causing unroutability or long detours which hurt timing. Reduce it via cell spreading, macro re-placement, increasing utilization margin, adding routing tracks, rerouting high-fanout nets, local buffering, or changing floorplan/IO placements. Also use blockages and routing guides to steer routing.
**Hiring manager listening for:**

* Concrete tactics used to resolve congestion.
* Ability to diagnose (heatmaps, router reports).
* Preventive placement choices and tool knobs.

---

## 🟩 FLOORPLANNING QUESTIONS

### 11. What factors decide macro placement?

**Answer:** Factors include IO location, power/ground requirements, heat/dissipation, timing-critical proximity to logic, accessibility for routing, coupling/noise isolation from analog, and re-use/port constraints (pin access). Also floorplan power rails and keep-out zones shape placement.
**Hiring manager listening for:**

* Multi-discipline thinking: thermal, power, timing, EMC.
* Trade-offs when placing memories vs. logic.
* Macro orientation and pin-access strategies.

### 12. What is the halo around macros?

**Answer:** A halo is reserved whitespace around macros to give routing channels and prevent congesting nearby standard cells — it helps with pin access, reduces local congestion, and provides space for decaps and power contacts.
**Hiring manager listening for:**

* How halo size is chosen (pin density, routing demand).
* Impact on utilization and local routing.
* When to reduce or enlarge halos.

### 13. What are **blockages** (soft, hard, partial)?

**Answer:** Blockages restrict placement/routing in certain areas. Hard blockages forbid any routing/placement (e.g., keep-outs), soft blockages allow limited routing or placement with constraints, and partial blockages restrict specific layers or cell types. They guide tools around macros, IO, thermal sensors.
**Hiring manager listening for:**

* Use cases for each type and how they influence tools.
* Practical examples (RF shields, vias, reserved keepouts).
* Interaction with router and legalizer.

### 14. How do you fix **pin accessibility issues**?

**Answer:** Fixes: reorient macros/pins, add local routing channels or halo, use via/via-fills, create pin-swaps in macro if allowed, use multi-layer routing or reroute congesting neighbors, and in some cases change macro placement. Early pin accessibility checks during floorplan avoid late fixes.
**Hiring manager listening for:**

* Tools/reports used to detect issues.
* Practical, least-impactful fix-first mindset.
* Examples with memory or IO pins.

### 15. What is a **power strap** and how do you decide strap width/spacing?

**Answer:** Power straps are wide metal traces connecting power rails across the chip to build the power grid. Width/spacing is sized for current density (IR/EM limits), manufacturing rules (density, spacing), and voltage droop targets — calculated from current draw, segment length, and allowable voltage drop.
**Hiring manager listening for:**

* EM/IR considerations and basic sizing equations.
* Use of power rings, vias, and stitching.
* How to iterate using IR/EM analysis.

### 16. Explain **IR drop** and fixes (power grid strengthening, decaps).

**Answer:** IR drop is the voltage lost across the metal/wire resistance under current causing lower-than-expected Vdd at cells. Fixes: strengthen power grid (wider straps, more vias), add local power rails, add decoupling capacitors (decaps) to reduce transient droop, floorplan power domains, and redistribute current-dense blocks.
**Hiring manager listening for:**

* Static vs dynamic/localized droop and fixes.
* Role of decaps in transient conditions.
* Practical iteration with power analysis tools.

### 17. What is the purpose of **decap cells**?

**Answer:** Decap cells (decoupling capacitors) supply local charge to reduce transient voltage droop and stabilize the power rail during switching events. They help at high frequencies where package/PDN inductance causes localized droop.
**Hiring manager listening for:**

* Placement strategy (near buffers, macro clusters).
* Trade-off between area and decap benefit.
* Interaction with package/IC PDN.

### 18. What is **antenna effect** and how to fix it?

**Answer:** Antenna effect: during fabrication, long metal segments can accumulate charge and damage gate oxides. Fixes include antenna diodes, antenna routing rules (break long interconnects), gate/source-drain connect order, or process-specific antenna fixes (via insertion or re-routing).
**Hiring manager listening for:**

* Awareness of manufacturing step issues.
* Familiarity with design-rule-based fixes and when to apply them.
* Examples of antenna diodes and routing changes.

### 19. Explain **CTS balancing logic**.

**Answer:** CTS balancing ensures equal or controlled clock latency from root to sinks to meet skew and latency objectives. This includes inserting buffers, matching path delays, controlling sink insertion points, and tuning tree topology. It balances clock insertion delay and minimizes skew and jitter impact.
**Hiring manager listening for:**

* Tools/metrics for balancing (skew/latency windows).
* Trade-off between balanced tree and useful skew.
* Examples of fanout buffering and clustering.

### 20. How do you create a **clock mesh** vs. **clock tree**?

**Answer:** Clock tree: hierarchical buffered distribution (H-tree, buffered branches) optimized for low insertion delay and controlled skew using CTS tools. Clock mesh: dense grid (often physically connected) providing multiple paths and robustness to variation; typically used in high-performance cores (mesh may be synthesized with H-tree overlay). Choice depends on jitter, variation tolerance, and power budget.
**Hiring manager listening for:**

* Pros/cons: mesh robustness vs power/area cost.
* Use cases: CPU cores vs IO/clocks.
* Understanding of synthesis and signoff differences.

---

## 🟧 PLACEMENT & CTS QUESTIONS

### 21. What is **legalization** after placement?

**Answer:** Legalization snaps placed cells to legal cell sites and resolves overlaps produced by global placement, adhering to row, orientation, and fence constraints. It may adjust placement locally to satisfy design rules before detailed placement and routing.
**Hiring manager listening for:**

* How legalization impacts timing and congestion.
* Techniques to minimize movement and timing impact.
* Experience with tool options for legalization.

### 22. What is **cell spreading**?

**Answer:** Cell spreading increases whitespace by redistributing cells across the core to reduce local congestion and improve routability. It's used when utilization is high in localized regions to ease routing and reduce violation hotspots.
**Hiring manager listening for:**

* How to apply selectively vs globally.
* Impact on timing and presence of macros.
* Balancing target utilization against wirelength.

### 23. How do you minimize **routing congestion** during placement?

**Answer:** Techniques: insert whitespace (spreading), floorplan adjustment, pin reorientation, staggered macro placement, create routing channels, use congestion-aware placement algorithms, route high-fanout nets early, and use layer assignment/power planning to free routing tracks.
**Hiring manager listening for:**

* Concrete proactive steps vs reactive fixes.
* Using router reports and congestion maps.
* Examples where placement change fixed routing.

### 24. Define **skew**, **latency**, and **uncertainty**.

**Answer:** Skew = difference in arrival times of the clock at two sinks. Latency = absolute delay from clock source to a sink. Uncertainty = non-deterministic variation in clock edges (e.g., launch/arrival jitter, CDC tool insertion, or insertion delay variation). STA budgets use skew and uncertainty with setup/hold equations.
**Hiring manager listening for:**

* Correct use in timing equations.
* Sources of uncertainty (clock insertion, CDC).
* How to measure and control each.

### 25. Why do we do **pre-CTS optimizations**?

**Answer:** Pre-CTS optimization reduces downstream work and timing risk by fixing long combinational paths, buffering, reducing congestion, and preparing balanced sink clusters so CTS can produce a better tree. It reduces iterative post-CTS fixes.
**Hiring manager listening for:**

* Examples of pre-CTS fixes.
* How pre-CTS reduces total iterations.
* Trade-offs and timing impact.

### 26. What is **useful skew**?

**Answer:** Useful skew is intentionally introduced skew to improve timing margin by skewing clock arrival at flop pairs so that data propagation benefits (e.g., creating a late clock at the receiving flop to meet setup or early clock for hold). It's a timing optimization technique when safe per path analysis.
**Hiring manager listening for:**

* How to identify safe useful skew opportunities.
* Risk of unintended negative impact on other paths.
* Implementation methods (buffer insertion, path tuning).

### 27. Explain **H-tree** clock distribution.

**Answer:** H-tree is a symmetric, binary-branch clock distribution topology that balances path lengths to sinks, minimizing skew. It's commonly used in synchronous cores to provide uniform clock insertion delay and is a standard topology for fixed grid clocking.
**Hiring manager listening for:**

* Pros/cons compared to mesh.
* Implementation details and use in CTS tools.
* Handling CT buffers and leaf insertion.

### 28. What causes **clock divergence**?

**Answer:** Clock divergence arises from unequal clock path delays due to placement variations, buffer sizing, skew from routing, temperature/IR-induced delay changes, or mismatches in clock gating insertion. Bad CTS topology or asymmetric loading exacerbates divergence.
**Hiring manager listening for:**

* Ability to diagnose divergence causes (reports, net analysis).
* Mitigation strategies (rebalancing, rebuffering).
* Awareness of process variation effects.

### 29. How do you optimize high-fanout nets?

**Answer:** Use buffered tree structures (fanout buffers), repeater insertion, logical restructuring into multi-level nets, RC-aware buffering, or use specific toolkit features (synthesis buffer insertion for high-fanout nets). Also place buffers strategically to reduce slew and crosstalk.
**Hiring manager listening for:**

* Trade-offs: area vs timing vs power.
* Buffer sizing and placement strategy.
* Tools and commands commonly used.

### 30. How do you fix **clock gating timing violations**?

**Answer:** Fix by ensuring gating cell (enable) is timed correctly — use insertion of isolation cells, ensure enable meets required set-up/hold with proper constraints, re-time gating signals, or use clock gating aware synthesis and CTS that considers gated clocks as separate domains. If glitching, add level-sensitive latches or reposition gating cells.
**Hiring manager listening for:**

* Knowledge of clock-gating cell libraries and insertion timing rules.
* Examples of fixes for setup/hold on enables.
* Awareness of gating and CDC interactions.

---

## 🟥 ROUTING QUESTIONS

### 31. Explain **global routing** vs **detailed routing**.

**Answer:** Global routing plans coarse routes and layer assignment, estimating congestion and resource usage without exact geometries. Detailed routing assigns exact wires/vias per metal grid obeying DRCs and finalizes geometry. Global routing guides the detailed router to achieve feasible routability.
**Hiring manager listening for:**

* Understanding of abstraction levels and their outputs.
* How global routing influences timing estimates.
* Experience handling global routing congestion hotspots.

### 32. What is **DRC**?

**Answer:** Design Rule Check — a set of foundry-specified geometric rules (spacing, width, enclosure, density) that the layout must meet for manufacturability. DRC violations must be fixed before tapeout.
**Hiring manager listening for:**

* Types of common DRCs (spacing, via enclosure).
* Tooling and signoff flow.
* How you debug and fix DRCs.

### 33. What is **min spacing**, **min width**, **notch**, **via enclosure**?

**Answer:** Min spacing = minimum allowed distance between shapes. Min width = minimum metal width for process reliability. Notch = small indentation violating spacing/width rules (can cause DRC). Via enclosure = requirement that vias are covered by sufficient metal extension. All are dictated by process design rules.
**Hiring manager listening for:**

* How these rules cause routing failures.
* Fix strategies (wider tracks, re-route).
* Awareness of manufacturing sensitivity.

### 34. What are **cut layers**?

**Answer:** Cut layers are layers where vias or contacts are placed to connect adjacent metal layers (e.g., via1, via2). They have their own DRCs (enclosures, spacing) and are critical for routing transitions and reliability.
**Hiring manager listening for:**

* Impact on via resistance, EM, and reliability.
* Planning via usage to minimize via stacking risks.
* Understanding of cut-layer rules.

### 35. What is **wire resistance vs capacitance** impact on timing?

**Answer:** Resistance increases RC time constant, slowing signals and causing IR drop; capacitance increases load, slowing transitions and increasing dynamic power. Longer wires mean more RC delay (dominant in advanced nodes), so routing must minimize long RC-heavy runs and use upper metals with lower R.
**Hiring manager listening for:**

* Explanation of RC delay and distributed RC effects.
* Use of repeaters and upper metals for long runs.
* Trade-offs vs area and power.

### 36. Why are upper layers thicker?

**Answer:** Upper metal layers are thicker (lower sheet resistance) to carry long-distance signals and large currents with lower RC delay. Thicker metals reduce resistance, enabling faster global nets and power distribution.
**Hiring manager listening for:**

* Practical use of upper layers for clocks, power, global signals.
* How layer assignment affects timing.
* Via planning between layers.

### 37. How do you minimize **crosstalk** during routing?

**Answer:** Increase spacing between aggressor/victim nets, use shielding (ground/power rails between nets), route noisy/high-speed nets on separate layers, change routing direction, reduce simultaneous switching, and use timing-driven routing to avoid parallel runs of critical nets.
**Hiring manager listening for:**

* Which nets to prioritize for shielding.
* Impact of crosstalk on timing and functional failure.
* Tool knobs and routing strategies.

### 38. Explain **shielding** and **double-width routing**.

**Answer:** Shielding inserts grounded/power nets between critical signals to reduce coupling. Double-width routing uses wider wires for important nets to reduce resistance and inductive coupling. Both reduce crosstalk and improve signal integrity but consume more routing resources.
**Hiring manager listening for:**

* Practical trade-offs (area vs noise mitigation).
* Examples (clock shielding).
* Interaction with DRC/density rules.

### 39. What is **timing-driven routing**?

**Answer:** Routing that prioritizes timing-critical nets by allocating better routes (shorter, less capacitive layers), using timing cost functions to steer router decisions, and resolving timing violations directly in routing rather than post-route fixes.
**Hiring manager listening for:**

* How timing-driven routing differs from general routing.
* Examples of router constraints (timing cost weight).
* When to apply timing-driven routing.

### 40. What causes via failures and how to avoid them?

**Answer:** Via failures are caused by EM due to high current density, poor via enclosure, manufacturing stress, or thermal cycling. Avoid with proper via sizing, via arrays for current sharing, obeying via spacing/enclosure rules, and distributing via usage to lower current per via.
**Hiring manager listening for:**

* EM awareness and via redundancy.
* Use of via arrays and current calculations.
* Integration with signoff EM checks.

---

## 🟪 STATIC TIMING ANALYSIS (STA) QUESTIONS

### 41. Define **setup violation** and how to fix it.

**Answer:** Setup violation occurs when data doesn't arrive at the capturing flop before the clock sampling edge plus setup time. Fixes: reduce data path delay (re-buffer, re-size, re-synthesize), increase clock period, introduce useful skew, re-route to reduce RC, restructure logic, or move flops closer.
**Hiring manager listening for:**

* Range of concrete fixes prioritized by impact.
* Awareness of PVT corner dependency.
* Use of STA reports and path analysis.

### 42. Define **hold violation** and how to fix it.

**Answer:** Hold violation occurs when data changes too soon after the clock edge, violating the required hold window. Fixes: add delay on data path (buffers/re-timing), slow down clock path (insert delay in clock tree), enable hold fix via tool (hold buffers), or adjust constraints (only after validating).
**Hiring manager listening for:**

* Awareness that hold fixes must not break setup.
* Use of clock path tweaks or datapath buffers.
* Tool primitives for hold fixing.

### 43. Explain **setup equation** and **hold equation**.

**Answer:** Setup: `Tclk >= Tcomb + Tskew + Tsu + Tjitter + Tuncertainty` (simplified). Hold: `Tcomb_min + Thold <= Tclk_edge_diff + Tskew - Tuncertainty` (or data path must remain stable for hold time). They capture the relationship between clock, data delays, skew, and margin.
**Hiring manager listening for:**

* Ability to write and interpret the equations.
* Including OCV/uncertainty/jitter correctly.
* How to apply them to fixes.

### 44. What is **OCV**, **AOCV**, **POCV**?

**Answer:** OCV = On-Chip Variation (static margin added to timing to account for intra-die variation). AOCV = Advanced OCV (path-based variation accounting for local variability). POCV = Process OCV (another variant handling process-induced variation). Different methodologies model variation differently in STA.
**Hiring manager listening for:**

* Awareness of signoff variation models.
* When to use AOCV vs OCV.
* Impact on timing margins and pessimism.

### 45. What is **PVT corner**?

**Answer:** PVT = Process, Voltage, Temperature corner combinations used in STA to ensure design works across manufacturing/process shifts, supply variations, and temperature extremes (e.g., slow-slow, fast-fast, typical). Each corner tests different timing and power scenarios.
**Hiring manager listening for:**

* Examples of corners and their significance.
* How corners affect STA and signoff.
* Which corners are critical for setup vs hold.

### 46. What is **clock reconvergence pessimism** (CRP)?

**Answer:** CRP arises when STA pessimistically counts reconvergent clock path differences because analyzer assumes worst-case combining of clock uncertainties. It leads to overly pessimistic timing. Tools offer CRP reduction techniques to avoid over-pessimism.
**Hiring manager listening for:**

* How CRP affects multi-branch clocks.
* Mitigation techniques (CRP reduction, better modeling).
* Examples of when it's critical.

### 47. How do you apply **multi-cycle path constraints**?

**Answer:** Use SDC (`set_multicycle_path`) to tell STA that a path can take multiple clock cycles, which relaxes setup and tightens hold accordingly. Ensure verification with clock domains and latches, and validate no unintended paths are affected.
**Hiring manager listening for:**

* Correct SDC usage and examples.
* Awareness of launch/capture semantics.
* Validating the constraint scope.

### 48. What is a **false path**?

**Answer:** False path is a logic path that cannot occur in actual operation (e.g., gated signals, functional constraints). Marking it (`set_false_path`) prevents STA from wasting effort and producing meaningless violations; be cautious to avoid masking real failures.
**Hiring manager listening for:**

* How to identify legitimate false paths.
* Risks of over-marking false paths.
* Using lint or functional checks to justify them.

### 49. Explain **data-to-data** and **clock-to-clock paths**.

**Answer:** Data-to-data paths: sequential elements where both launch and capture are data elements (e.g., flop to flop through combinational logic). Clock-to-clock paths involve paths where clock signals pass between elements (rare but relevant in gated clock/clock domain crossings). STA treats them differently in constraints and analysis.
**Hiring manager listening for:**

* Examples and why they matter.
* How tools interpret non-standard path types.
* Constraint treatment.

### 50. How do you fix negative slack in post-route STA?

**Answer:** Prioritize fixes: identify critical paths; optimize routing for reduced RC; buffer/re-size cells; restructure logic; apply ECOs (cell swaps, net swaps); introduce useful skew or clocking changes; or as last resort, re-floorplan or relax constraints. Ensure fixes are validated across corners.
**Hiring manager listening for:**

* Systematic triage approach.
* Awareness of routing-induced delays and extraction effects.
* Use of incremental signoff checks.

---

## 🟫 SIGNOFF QUESTIONS (DRC, LVS, EM/IR)

### 51. Difference between **DRC** and **LVS**.

**Answer:** DRC checks geometric/manufacturing rules (spacing, widths); LVS (Layout vs Schematic) verifies that the netlist of the layout matches the intended schematic/netlist (connectivity and device matching). Both are required for manufacturability and functional correctness.
**Hiring manager listening for:**

* Clear differentiation and their signoff order.
* Examples of LVS mismatches (missing connections).
* Toolflow familiarity.

### 52. What is **ERC**?

**Answer:** ERC = Electrical Rule Check — verifies electrical-level rules such as well connections, floating nodes, pin pull-ups, and voltage domain misuse (e.g., analog/digital violations). It complements DRC/LVS by catching electrical issues not covered by geometric rules.
**Hiring manager listening for:**

* Examples of ERC catches.
* How ERC integrates into signoff.
* Fix strategies.

### 53. Explain **EM (Electromigration)** — causes & prevention.

**Answer:** EM is metal migration caused by high current density over time, leading to open circuits. Prevention: reduce current density (wider wires, via arrays), route current-carrying nets on thicker metals, add redundant vias, and adhere to EM limits and lifetimes. Validate with signoff EM tools.
**Hiring manager listening for:**

* Calculation awareness (current per via).
* Via array and wire sizing practices.
* Use of signoff checks and margins.

### 54. What is **IR drop**? Static vs dynamic.

**Answer:** Static IR drop = DC voltage drop under average current draw; dynamic droop (voltage droop) = transient voltage drop during switching due to inductance and limited decoupling. Both reduce effective Vdd and can cause timing failures or functional issues.
**Hiring manager listening for:**

* Difference and mitigation strategies.
* Role of package PDN and simulation.
* Practical design fixes.

### 55. What is **voltage droop**?

**Answer:** Voltage droop is transient Vdd reduction during switching events caused by PDN impedance and switching current surges. It is mitigated by decaps, low-impedance PDN design, and distributed power straps.
**Hiring manager listening for:**

* Examples (rush of switching causing transient).
* How decaps and package help.
* Measurement/validation methods.

### 56. How do decap cells reduce IR drop?

**Answer:** Decaps provide a local charge reservoir that supplies instantaneous current during switching, reducing the transient voltage dip (dynamic droop). They do not reduce DC IR but smooth fast transients and reduce high-frequency impedance.
**Hiring manager listening for:**

* Correct role: transient mitigation, not DC IR cure.
* Placement near hotspots.
* Trade-offs for area.

### 57. What causes **LVS mismatches**?

**Answer:** Causes: incorrect pin naming, missing or extra vias, parameter mismatches, parasitic devices, illegal connectivity created during layout, or GDS extraction errors. Fix by comparing layout netlist vs schematic and correcting connectivity or device parameters.
**Hiring manager listening for:**

* Debug process and tools.
* Typical mistakes (copy/paste macro pin mapping).
* Steps to prevent during layout.

### 58. What are **antenna violations**? Fixes?

**Answer:** Antenna violations arise when long metal runs during fabrication cause charge accumulation on gates, risking damage. Fixes: add antenna diodes, change routing to break long metal segments, insert vias early, or modify design to adhere to antenna ratio limits.
**Hiring manager listening for:**

* Process-specific antenna metrics.
* Practical fixes and automation use.
* Examples where antenna fixes changed routing.

### 59. What is **dummy metal filling**?

**Answer:** Dummy fill inserts metal shapes in empty areas to meet local density rules and improve planarity during CMP. Must be inserted respecting DRCs and later excluded in parasitic extraction or modeled accurately for EM/IR impacts.
**Hiring manager listening for:**

* Awareness of density rule impacts and fill strategies.
* Ensuring parasitic extraction remains accurate.
* CMP/planarity reasoning.

### 60. What is **density rule** in manufacturing?

**Answer:** Density rules enforce minimum and maximum local metal density across a chip to ensure uniform CMP and avoid topography issues. Violations require fill or removal to meet foundry specs.
**Hiring manager listening for:**

* Ability to incorporate fill without hurting routing/timing.
* Understanding of DRC tool support.
* Real examples of density fixes.

---

## 🔥 ADVANCED PDE QUESTIONS

### 61. How do you close timing on a critical long path that fails across multiple corners?

**Answer:** Multi-pronged approach: (1) analyze path across corners to find common bottlenecks; (2) logic restructuring or retiming; (3) buffer insertion and sizing targeted for worst corners; (4) move flops to reduce routing; (5) apply multi-Vt or speed cells on critical paths; (6) if routing-induced, prioritize routing or adjust layer assignment; and (7) as last resort, relax constraints or change floorplan. Validate across corners iteratively.
**Hiring manager listening for:**

* Systematic, corner-aware closure steps.
* Use of multi-Vt, gate sizing, and placement changes.
* How to prioritize non-invasive to invasive fixes.

### 62. How do you handle **multi-Vt optimization**?

**Answer:** Multi-Vt uses low-Vt cells for speed-critical paths and high-Vt for leakage-critical non-critical areas. Apply Vt assignment during synthesis/physical optimization using timing slack maps, verify impact on shift in timing and leakage, and ensure IR/EM and variability effects are acceptable. Use tool support to swap cells and re-run STA iteratively.
**Hiring manager listening for:**

* Tradeoffs of leakage vs speed and methodology to assign.
* Awareness of timing vs variability effects.
* Toolchain steps for cell swapping.

### 63. Explain **clock tree robustness** under variation.

**Answer:** Robustness means clock insertion is insensitive to PVT/IR/CTS variations: use redundancy (mesh/dual-tree), minimize skew sensitivity, add margin for jitter/uncertainty, use symmetric buffering, consider AOCV, and design the PDN to minimize clock droop. Validate with variation-aware signoff (Monte Carlo, LVS/RC).
**Hiring manager listening for:**

* Concrete validation strategies.
* Knowledge of mesh and hybrid clocking benefits.
* Awareness of IR/jitter coupling.

### 64. What is the difference between **mesh**, **H-tree**, **spine**, and **hybrid** clocks?

**Answer:** H-tree = balanced buffered tree. Mesh = dense grid offering multiple paths and variation robustness. Spine = central routing spine with branches. Hybrid = combination (H-tree for locality + mesh overlay for robustness). Choice depends on skew/jitter, power budget, and process variation tolerance.
**Hiring manager listening for:**

* Pros/cons and use-case examples.
* Power/area trade-offs.
* Implementation and signoff differences.

### 65. How do high-frequency chips reduce jitter?

**Answer:** Reduce supply noise, use low-noise PLL design, reduce clock insertion jitter by symmetric buffering and shielding, use cleaner PDN, use high-quality clock sources, reduce crosstalk on clock nets, and optimize clock buffers/trees for low phase noise. Also use timing budgeting for jitter in STA.
**Hiring manager listening for:**

* Awareness of noise sources and PDN interaction.
* Clock path design choices.
* Measurement/validation techniques.

### 66. What is **CTS clustering**?

**Answer:** CTS clustering groups sinks/flip-flops into clusters so the CTS tool can synthesize local subtrees, improving scalability and managing skew within clusters. Clustering is used to control resource usage and timing optimization granularity.
**Hiring manager listening for:**

* How cluster size affects skew and routing.
* Practical heuristics for clustering.
* Tool commands/experience.

### 67. Explain **RC extraction** types: C-only, RC, Asymmetric RC.

**Answer:** C-only extraction produces capacitances only (fast and less pessimistic), RC extraction provides both resistance and capacitance for delay and EM analysis, and asymmetric RC captures direction-dependent effects (important for non-symmetric routing and coupling). As nodes scale, RC/asymmetric models are more accurate for timing.
**Hiring manager listening for:**

* When each model is used and trade-offs (accuracy vs runtime).
* Signoff implications.
* Examples from advanced nodes.

### 68. How do you reduce power in physical design?

**Answer:** Techniques: clock gating, multi-Vt, power gating, use low-power libraries, reduce switching via logic optimization, place high-switching blocks to reduce wirelength, optimize voltage islands, and aggressive power-aware placement/routing and gate sizing. Also optimize cell libraries and apply dynamic voltage/frequency scaling architecture.
**Hiring manager listening for:**

* Concrete layout-level optimizations.
* Awareness of impact on timing/EM/IR.
* Power signoff considerations.

### 69. Discuss timing challenges in **7nm/5nm FinFET** nodes.

**Answer:** Challenges: higher sensitivity to variability (random dopant/line-edge), tighter pitch causing routing congestion, increased parasitic coupling, lower SRAM margin, power density/thermal constraints, and complex multi-patterning or EUV issues. Requires careful placement, variation-aware timing, and more aggressive shielding and buffer strategies.
**Hiring manager listening for:**

* Node-specific technical issues.
* How to adapt flows (AOCV, parasitic-aware optimizations).
* Practical fixes used in recent designs.

### 70. What is **double patterning** and **EUV**?

**Answer:** Double patterning splits critical patterns into two masks to overcome lithographic resolution limits (increasing design complexity and overlay constraints). EUV is Extreme Ultraviolet lithography enabling single-patterning for some layers — reduces some complexity but has its own constraints (stochastic defects). Both influence layout rules and design restrictions.
**Hiring manager listening for:**

* Manufacturing impacts on layout (coloring, spacing).
* Practical constraints and design adaptations.
* Awareness of process evolution.

---

## 🧠 SCENARIO-BASED PDE QUESTIONS

### 71. Your design fails hold in FF corner after routing — what do you do?

**Answer:** Diagnose paths with hold violations, inspect clock arrival vs data min path, add small buffers on data paths or increase delay on clock via buffer insertion or slowing clock path, use hold fix tool, and ensure fixes don’t break setup. If routing created short RC, add delay cells or re-route to increase net delay. Re-run hold across corners.
**Hiring manager listening for:**

* Quick triage steps and hold-first mindset.
* Awareness of minimal invasive fixes.
* Validation across corners.

### 72. Congestion at macro corners — fixes?

**Answer:** Move macros slightly, increase halo, add local routing channels, spread nearby cells, use pin re-orientation, add metal routing around macro, or change macro orientation. If possible, adjust macro floorplan or create dedicated power/decap placement to free routing.
**Hiring manager listening for:**

* Practical placement/reroute fixes.
* Consideration of macro pin accessibility.
* Willingness to revisit floorplan when necessary.

### 73. IR drop is high in a local region — what steps will you take?

**Answer:** Identify current sources, add/resize power straps and vias, insert additional decaps nearby, redistribute high-current blocks, add local power rails, and check package PDN. Run EM/IR signoff to ensure fixes meet limits. Consider local Vdd tap or power domain changes.
**Hiring manager listening for:**

* Systematic diagnosis of PDN.
* Concrete sizing/via strategies.
* Awareness of transient vs static issues.

### 74. Clock skew is too high in a sub-block — fixes?

**Answer:** Rebalance CTS locally (rebuffer, adjust branch points), move flops to equalize distances, reduce load on skewed branch, add deskew buffers, or re-cluster sinks. Ensure power/IR issues are not causing variable delays. Re-run CTS with tighter constraints.
**Hiring manager listening for:**

* Local vs global fixes and considerations.
* Use of CTS tools/options for rebalancing.
* Cross-check with IR/em and routing.

### 75. Setup is clean but hold is failing badly — root cause?

**Answer:** Often caused by insufficient clock path delay (data arrives too quickly), routing shortening data path, or CTS too fast for certain branches. Could also be due to changes from routing reducing net delay. Fix by adding delay to data or clock path or inserting hold buffers.
**Hiring manager listening for:**

* Awareness of routing-induced hold issues.
* Non-destructive fix preferences.
* Validation approach to avoid breaking setup.

### 76. Memory macro has inaccessible pins — how do you fix it?

**Answer:** Reorient macro, use pin swapping if permitted, create local routing channels and halo, move nearby cells, add micro-vias or fill vias earlier, or use port re-assignment to access pins. If macro has programmable pin locations, update macro placement options.
**Hiring manager listening for:**

* Practical fixes and ordering preference.
* Macro vendor coordination knowledge.
* Ability to trade-off area vs access.

### 77. Routing DRCs explode after CTS — why?

**Answer:** CTS changes routing topology, places many clock buffers and buffers’ routes that can toggle routing density leading to DRCs (notches, spacing). Excessive buffer insertion or poor layer assignment can cause density hotspots. Fix by using routing guides, adjusting CTS constraints for buffer placement, and iterating placement/routing.
**Hiring manager listening for:**

* Link between CTS and routing density.
* Steps to resolve without destroying timing.
* Use of detailed routing constraints.

### 78. Clock gating cells cause glitches — how to solve?

**Answer:** Ensure gating enable meets timing (synchronous enable), use integrated clock gating cells (with latches) from library, add isolation cells or handshake logic, verify that gating doesn’t create combinational feedback, and run functional validation and STA. Re-synthesize gating if necessary.
**Hiring manager listening for:**

* Familiarity with gated cell libraries and insertion rules.
* Handling of functional and timing aspects.
* Debug methodology.

### 79. Too many vias on one net — how to optimize?

**Answer:** Consolidate via usage with via arrays, use alternate routing layers to reduce layer transitions, reorder routing to avoid multiple stacked vias, or reassign routing priority. Use router settings to limit via insertion or manual via optimization.
**Hiring manager listening for:**

* Via array use and EM awareness.
* Practical router commands and constraints.
* Balance between manufacturability and timing.

### 80. Metal density violations — how do you fix?

**Answer:** Add or remove dummy fills, redistribute routing to balance density, add shielding or reroute non-critical nets, and sometimes change macro orientation to spread metal. Work with fill tool settings to obey density windows.
**Hiring manager listening for:**

* Use of fill tools and DRC-driven strategies.
* Awareness of parasitic impact.
* Examples of successful fixes.

---

## 🟧 TOOLS QUESTIONS (Cadence, Synopsys, OpenROAD/OpenLane)

### Cadence Innovus questions

### 81. What is `place_opt` vs `optDesign`?

**Answer:** `place_opt` is typically a placement optimization step (legalization, optimization of wirelength/congestion), while `optDesign` is a broader optimization command that may include placement, sizing, buffering, and timing-driven optimizations. Exact names/flags vary by tool version — check the tool manual.
**Hiring manager listening for:**

* Understanding tool command purposes, not just names.
* Examples of what each optimizes.
* Familiarity with Innovus flow.

### 82. What is `setOptMode` used for?

**Answer:** `setOptMode` sets optimization modes (performance, area, power, or balanced) to guide subsequent optimization commands, altering algorithm priorities and heuristics. It helps tailor the optimization to design goals.
**Hiring manager listening for:**

* How modes affect results.
* Use-cases for switching modes mid-flow.
* Tool experience.

### 83. What is `ctsSpec`?

**Answer:** `ctsSpec` supplies CTS constraints and specifications (buffer types, skew/latency limits, root placement, sink clustering, buffers per branch) to guide clock tree synthesis behavior in Innovus.
**Hiring manager listening for:**

* Knowledge of CTS knobs and practical settings.
* How to tune for skew/jitter and power.

### 84. What is `optDesign -postRoute`?

**Answer:** `optDesign -postRoute` runs design optimizations that consider routing information (post-route optimizations), such as resizing, rebuffering, or incremental ECOs informed by post-route RC to close timing or fix violations.
**Hiring manager listening for:**

* Role of post-route optimization and its risks.
* Examples of changes made at this stage.

### 85. Explain `timeDesign -signoff`.

**Answer:** `timeDesign -signoff` runs timing analysis and optimization tuned for signoff quality (tight timing models, extraction-driven analysis, and conservative checks) preparing the design for final validation. It usually enables signoff-quality checks and constraints.
**Hiring manager listening for:**

* Difference between signoff and initial timing runs.
* Steps you take before running signoff.

### Synopsys ICC2 questions

### 86. Difference between Fusion Compiler and ICC2?

**Answer:** Fusion Compiler integrates synthesis and place-and-route in one environment enabling tighter synthesis↔PnR loops. ICC2 is Synopsys’ traditional physical implementation tool focused on placement and routing. Fusion may offer faster iterative optimizations by integrating front-end and back-end.
**Hiring manager listening for:**

* Advantages of integrated flow vs separated.
* Practical experience and limitations.

### 87. What is `clock_opt`?

**Answer:** `clock_opt` optimizes clock tree parameters (buffering, skew, insertion delay) to meet timing and skew constraints. It may rebuffer or reassign clock routes for better timing.
**Hiring manager listening for:**

* Familiarity with clock optimization strategies.
* Examples of clock_opt outcomes.

### 88. What is `route_auto`?

**Answer:** `route_auto` triggers automated routing with default or user-specified routing strategies (global + detailed routing), using tool heuristics to complete routing based on current design constraints.
**Hiring manager listening for:**

* How to tune route_auto for critical nets.
* Dealing with routing failures.

### 89. What is `check_design`?

**Answer:** `check_design` runs a suite of checks (DRC-like, connectivity, placement rules) within ICC2 to ensure design health before routing/signoff. It helps catch basic violations early.
**Hiring manager listening for:**

* Use as a pre-flight check.
* Typical issues caught.

### OpenRoad/OpenLane (if using Sky130)

### 90. What is `pdngen`?

**Answer:** `pdngen` generates power delivery network (PDN) structures (power rails, straps) in the OpenROAD/OpenLane flow for Sky130, creating power rings and straps based on specification files.
**Hiring manager listening for:**

* PDN generation understanding and customization.
* Using PDN tools in open-source flows.

### 91. How do you adjust utilization in OpenLane?

**Answer:** Adjust utilization by changing placement parameters (placement density, target utilization in config files), or update constraints like `placement_utilization` and rerun placement steps in the OpenLane flow.
**Hiring manager listening for:**

* Familiarity with OpenLane configs and iterative changes.
* How utilization affects routing and timing.

### 92. How to generate SDC for multi-clock?

**Answer:** Create SDC clocks (`create_clock`) for each root with appropriate period/edges, specify groups, define false paths and multicycle paths, and add clock groups for relationships (`set_clock_groups`) for multi-clock domains in the SDC used by STA tools.
**Hiring manager listening for:**

* Correct SDC syntax and domain handling.
* Handling asynchronous crossings and CDC.

### 93. What is `repair_timing`?

**Answer:** `repair_timing` is a utility to perform timing fixes (buffer insertion, re-sizing) automatically based on timing reports. In OpenLane/OpenROAD it helps iterate on failing paths with automated ECOs.
**Hiring manager listening for:**

* Understanding of automated vs manual fixes.
* Risks of blind automated changes.

### 94. What is `dpl` (detail placement)?

**Answer:** `dpl` performs cell legalization and small adjustments to finalize placement at cell site granularity before routing, addressing immediate DRCs and making placement compatible with routing grids.
**Hiring manager listening for:**

* Role between global placement and routing.
* How detail placement affects timing.

### 95. Explain OpenSTA basic flow.

**Answer:** OpenSTA reads netlist and SDC, performs delay calculation (using Liberty timing models), runs STA across corners, reports violations, and supports constraint checks. It’s a lightweight STA tool used in open-source PnR flows.
**Hiring manager listening for:**

* Familiarity with inputs and outputs.
* Strengths/limitations relative to commercial STA tools.
* How to use it in an open-source flow.

---


