Below are **Physical Design (PD) + STA + Floorplanning + CTS + Routing + Sign-off** interview questions and answers tailored exactly to your resume.
These are the **exact style asked in AMD, NVIDIA, Qualcomm, Intel, Apple, Synopsys**.

---

# ✅ **PHYSICAL DESIGN INTERVIEW Q&A (Best for Product Companies)**

---

# **1. What is the difference between Floorplanning and Placement?**

**Answer:**

* **Floorplanning** defines the chip/block outline, aspect ratio, macro placement, power grid, pin positions, blockages and routing channels.
* **Placement** positions the standard cells inside the defined floorplan while optimizing timing, congestion, and power.

**Key point:** Floorplan decides “where things go”; placement decides “how cells are arranged efficiently”.

---

# **2. During floorplanning, what metrics do you check?**

**Answer:**

* **Utilization** (typically 60–80%)
* **Aspect ratio**
* **Macro placement & channel spacing**
* **Pin placement**
* **Power planning (PG grid width, strap pitch)**
* **Congestion hotspots**
* **IR drop early estimation**

---

# **3. Why do we need power planning early in PD?**

**Answer:**
Because IR drop and EM issues must be minimized before placement.
Early PG grid ensures:

* Uniform power delivery
* Reduced droop during switching
* Better EM reliability
* Lower risk of late-stage ECOs

---

# **4. What is Timing Closure? Why is it difficult?**

**Answer:**
Timing closure means meeting setup/hold constraints across all **corners, modes, PVT, and derates**.

It is difficult because:

* Variations at 5nm/7nm are huge
* SI aggressor/victim coupling
* Multi-cycle, false paths, async crossings
* Congestion causing routing detours
* Huge RC parasitics in post-route stages

---

# **5. What is the difference between Setup and Hold violations?**

**Setup:**

* Data must reach before the clock edge.
* Violated at **slow corners** (max delay path).

**Hold:**

* Data must remain stable after the clock edge.
* Violated at **fast corners** (min delay path).

---

# **6. How do you fix Setup violations?**

**Fix options:**

* Sizing up cells (higher drive strength)
* Buffer insertion
* Reducing logic depth (RTL-level)
* Reducing clock skew (useful skew)
* Improving placement locality
* Routing with lower resistance layers
* Reducing derates

---

# **7. How do you fix Hold violations?**

**Fix options:**

* Insert delay buffers
* Increase clock latency to the launching flop
* Downsize cells on the data path
* Use higher resistance routing layers
* Add routing detour

Hold must be fixed **before tapeout**, cannot be fixed in silicon.

---

# **8. What is CTS? What are its goals?**

**Answer:**
Clock Tree Synthesis builds a balanced tree between clock source and all sinks.

**Goals:**

* Minimize **skew**
* Minimize **latency**
* Reduce **clock power**
* Reduce **insertion delay**
* Avoid noisy routes
* Prevent DRV violations

---

# **9. What is the difference between H-tree, Spine, and Mesh?**

**H-tree**

* Symmetric → minimum skew
* Used in CPUs, GPUs

**Clock Spine**

* Good for long, thin blocks
* Moderate skew

**Clock Mesh**

* Best skew robustness
* High power

---

# **10. What are the major causes of congestion?**

**Answer:**

* Bad macro placement
* High cell density in a region
* Too many control signals
* Blockages near macros
* Poor strap planning
* High-pin density logic (crossbars, NoCs)

---

# **11. What is Crosstalk?**

**Answer:**
When switching of **aggressor nets** induces noise or delay on **victim nets** due to capacitive coupling.

**Effects:**

* Delay increase (setup/hold)
* Glitches
* Functional failures

---

# **12. What is IR Drop and how do you reduce it?**

**IR drop = I × R loss** in PG network.

**Reduction:**

* Wider straps
* More PG layers
* More vias
* Add decaps
* Reduce local density
* Clock gating

---

# **13. Difference between Static and Dynamic IR Drop?**

* **Static IR:** leakage + average current
* **Dynamic IR:** switching event-driven droop → more critical

---

# **14. What is EM (Electromigration)?**

Movement of metal atoms due to high current density → causes opens/shorts.

**Fix:**

* Wider metals
* Via arrays
* Spread high-current cells
* Reduce peak toggling

---

# **15. Why is Routing done in multiple stages? (Global, Track, Detail)**

Because:

* Global routing estimates capacity
* Track assignment aligns to metal tracks
* Detailed routing assigns exact wires/vias without DRCs

---

# **16. What are DRC and LVS?**

**DRC:** Layout rule violations (spacing, width, via, enclosure, density)
**LVS:** Ensures layout netlist = schematic netlist

---

# **17. What is Antenna Effect?**

Plasma charging during fabrication causes long metal wires to accumulate charge and damage gate oxides.

**Fix:**

* Antenna diodes
* Jogging metal
* Layer hopping
* Split routing

---

# **18. What is Multi-Corner Multi-Mode (MCMM) Analysis?**

Considers all combinations of:

* Corners (ss/tt/ff, voltage, temperature)
* Modes (functional, test, scan, sleep)

Ensures no timing violations across all scenarios.

---

# **19. What is ECO? Types of ECOs?**

ECO = Engineering Change Order

**Types:**

* Functional ECO (RTL change)
* Timing ECO
* CTS ECO
* Layout ECO
* Sign-off ECO

---

# **20. What is Useful Skew?**

Intentionally delaying clock arrival to improve setup timing on critical paths.

---

# **21. What is Clock Uncertainty?**

Includes jitter + skew margin.

Used in STA to ensure safe timing.

---

# **22. What is OCV, AOCV, and POCV?**

* **OCV:** fixed derate
* **AOCV:** derate based on path depth
* **POCV:** derate based on cell/location probability distribution

---

# **23. Why is POCV better at advanced nodes?**

Because variations at 5nm/7nm are spatial and statistical.
POCV models realistic distributions → tighter derates → easier closure.

---

# **24. What is a False Path?**

A path that will never be logically activated in real operation.

Example: two paths enabled by mutually exclusive signals.

---

# **25. What is a Multi-Cycle Path?**

Path that takes more than 1 cycle to propagate.

**SDC:**

```
set_multicycle_path 2 -from A -to B
```

---

# **26. How do you reduce Clock Power?**

* Clock gating
* Lower buffer/inverter count
* Local mesh instead of full mesh
* Higher metal layers
* Multi-bit flops
* Useful skew reduction

---

# **27. What is Decap? Why used?**

Decoupling capacitor cell.
Reduces dynamic IR drop by providing instantaneous charge near switching clusters.

---

# **28. What is the purpose of Tap Cells and Endcap Cells?**

* **Tap cells:** prevent well/substrate floating
* **Endcaps:** protect edge of standard cell rows from DRC

---

# **29. Why are Multi-bit flops used?**

* Lower clock power
* Less routing
* Better skew balance
* Reduced area

---

# **30. Explain your GPU PD project. (HR + Technical favorite)**

**Strong Answer:**
I implemented block-level physical design for a GPU compute tile using Innovus.
I defined the floorplan, macro placement, PG grid, and routing channels.
After placement and CTS, I optimized congestion using cell padding, halos, and tie-offs.
I closed timing at **500 MHz**, resolved IR drop using strap adjustments and decap insertion, and delivered **DRC/LVS clean** GDS using Calibre.

---

 complete and ready for top-tier company interviews
(**Qualcomm / Nvidia / AMD / Intel / Apple / Google / Broadcom / Synopsys / Cadence**)

I’ve structured it like a **full preparation kit**.

---

# ✅ **PART 1 — 50 ADVANCED PHYSICAL DESIGN QUESTIONS (5nm / 3nm focused)**

### **1. What changes in 5nm/3nm PD compared to 14nm/28nm?**

* Higher resistance per µm
* Higher via resistance
* Massive variation → POCV required
* IR drop more critical due to lower Vdd
* Clock tree and mesh must handle more skew
* BEOL stack has many narrow metals → routing harder

---

### **2. Why is RC parasitic impact much worse in 5nm?**

Because **metal width shrinks**, resistance increases → delay dominated by wire RC, not cell delay.

---

### **3. What is Line-Edge Roughness (LER)?**

Edge irregularity of metal lines at advanced nodes → causes variation, delay instability.

---

### **4. What is Double Patterning / Multi-patterning?**

Splitting metal layers into multiple masks to achieve smaller pitch.

---

### **5. What is via-pillar congestion?**

Overuse of vertical interconnects between M0-M2 → causes local IR and routing blockages.

---

### **6. How is IR Drop modeled differently at 5nm?**

* Dynamic IR becomes dominant
* Must model **vector-based switching**
* Requires RedHawk/Voltus + activity patterns
* Local droop can cause functional failure

---

### **7. Why is EM more severe at 5nm?**

Metal width ↓ → current density ↑ → electromigration risk ↑.

---

### **8. What is self-heating?**

FinFET devices trap heat → local temp rises → affects mobility and timing.

---

### **9. What is MIMCAP and why important?**

Metal-Insulator-Metal capacitors → provide decap in dense blocks (GPU, CPU tiles).

---

### **10. How do you mitigate power noise in a large GPU tile?**

* Uniform PG grid
* Many strap layers
* Clock gating
* Local decaps
* IR analysis per cluster
* Metal fill optimization

---

### **11. What is Cut Metal?**

Special cut layers required for patterning → must follow strict spacing rules.

---

### **12. What is track-based routing?**

Advanced nodes have fixed routing tracks → cell pins must align to tracks.

---

### **13. Why is Pin Access such a big challenge in 5nm?**

Smaller pins + fewer tracks → router cannot reach without DRCs.

---

### **14. What are X-cells?**

Cells optimized for power/area but with difficult pin accessibility.

---

### **15. What is Cell Padding?**

Leaving empty space around a cell to ease routing around it.

---

### **16. What is Pin Spreading?**

Repositioning pins of macros/IP to reduce congestion.

---

### **17. Why are Scan chains difficult at 5nm?**

Long chains → congestion + IR drop spikes during shift mode.

---

### **18. How do you model aging effects? (BTI/HCI)**

Use derates in STA that depend on temp, stress time, duty cycle.

---

### **19. What is local skew vs global skew?**

* Local: between nearby flops
* Global: across the chip
  Local skew is usually far more critical.

---

### **20. Why do GPUs use Clock Mesh?**

High-frequency + large tile → mesh gives extremely low skew.

---

### **21. Why is a full mesh avoided?**

Power overhead (10–20% clock power increase).

---

### **22. What is IR-aware CTS?**

Building the clock tree by considering local IR weak spots.

---

### **23. What is Crosstalk Delta Delay?**

Incremental delay caused by aggressor switching.

---

### **24. What is Noise-Aware Routing?**

Routing with SI constraints to avoid crosstalk on sensitive nets.

---

### **25. What is shielding?**

Routing ground/power wires alongside critical nets.

---

### **26. What is Wire Spreading?**

Increasing wire spacing to reduce coupling noise.

---

### **27. What is STA pessimism?**

Extra derates applied to cover modeling inaccuracy.

---

### **28. Why is POCV used?**

To reduce pessimism and reflect real variation distribution.

---

### **29. What is Timing ECO Flow?**

* Fix high fanout
* Cell upsizing
* Rebuffer paths
* Reduce skew
* Adjust constraints
* Move macros if needed

---

### **30. What is logic cone balancing?**

Distributing combinational stages to reduce long paths.

---

### **31. What is Retention flop?**

Special flop that retains state during power gating.

---

### **32. What is an Isolation Cell?**

Prevents X-propagation when a power domain shuts down.

---

### **33. What is UPF?**

Unified Power Format for defining multi-voltage domains.

---

### **34. What is PPA trade-off?**

Improving Performance increases Power/Area.

---

### **35. What is Resistance Mapping?**

Mapping metal resistance variation across die for sign-off.

---

### **36. Why is density fill important?**

For uniform metal density to avoid lithographic issues.

---

### **37. What is ESD protection impact on PD?**

Large ESD cells at top level → affects IR and routing.

---

### **38. What is SSO noise?**

Simultaneous switching output noise → local power droop.

---

### **39. Why is Temp inversion relevant at 5nm?**

Delay increases at *lower* temperature—opposite of traditional nodes.

---

### **40. What is LVT/HVT device selection?**

Trade-off: leakage vs speed.

---

### **41. What is End-to-End Latency?**

Latency from clock source to deepest leaf.

---

### **42. What is CTS clustering?**

Grouping sinks to build an organized tree.

---

### **43. Why use useful skew?**

To improve setup timing without changing datapath.

---

### **44. What is dummy metal fill impact?**

Increases parasitics → must be included in extraction.

---

### **45. What is ECO Rebuffering?**

Replace long wire with multiple buffers to reduce delay.

---

### **46. What is Glitch Power?**

Power from unnecessary toggles → critical at 5nm.

---

### **47. What is Non-Default Routing Rule (NDR)?**

Use wider/thicker metals for critical nets.

---

### **48. How do you debug SI violations?**

* Check aggressor switching
* Spread wires
* Add shielding
* Reduce coupling cap

---

### **49. What is Giga-scale PnR challenge?**

Large blocks (GPU tiles, NPU cores) → memory limits + runtime explosion.

---

### **50. What are the top 5 sign-off must-checks at 5nm?**

* DRV
* EM
* IR drop (static + dynamic)
* Crosstalk
* MCMM timing

---

# ✅ **PART 2 — STA-ONLY INTERVIEW BOOKLET (Most Important)**

### **1. Explain max vs min delay corners.**

* **Max delay → setup** (slow process, low voltage, high temperature)
* **Min delay → hold** (fast process, high voltage, low temperature)

---

### **2. What is clock reconvergence pessimism (CRPR)?**

Avoid double-counting skew on common clock path.

---

### **3. What is AOCV?**

Derate based on number of logic stages.

---

### **4. What is POCV?**

Path-delay modeled using statistical sigma distributions.

---

### **5. What is derating?**

Scaling delay to cover variation.

---

### **6. What is clock uncertainty?**

Includes jitter + skew margin.

---

### **7. What is path-based analysis (PBA)?**

Accurate STA on the worst path — used when graph-based (GBA) pessimistic.

---

### **8. What is Slack?**

Slack = Required time – Arrival time.

---

### **9. What is slews impact?**

Large slew → increases delay and coupling noise.

---

### **10. What is fanout violation?**

Drive strength insufficient for load.

---

### **11. What is latency balancing?**

Balancing launch/capture latencies to reduce skew.

---

### **12. Why is hold harder at lower nodes?**

Faster transistors → data arrives too quickly.

---

### **13. How do you fix multi-cycle path violations?**

Adjust constraints + check logic validity.

---

### **14. What is setup margin?**

Extra safety time beyond meeting target.

---

### **15. What is STA Black-boxing?**

Ignore internal timing (macro) and use boundary constraints.

---

---

# ✅ **PART 3 — Project-Based HR Answers (Qualcomm, Nvidia, Intel)**

### **HR Question:**

**Tell me about your GPU Physical Design project.**

### **Best Answer:**

“I worked on block-level PnR for a GPU compute tile using Innovus.
I defined the floorplan, placed macros and power grid, and optimized cell placement to avoid congestion.
After CTS, I closed timing at 500 MHz using targeted ECO buffering and cell sizing.
I also ran RedHawk for IR/EM, optimized strap width/spacing, and inserted decaps to reduce dynamic IR by 15%.
Finally, I delivered a clean DRC/LVS GDS.
This project strengthened my expertise in advanced-node timing closure, routing, and sign-off.”

---

### **HR Question:**

**Why do you want to join Qualcomm / Nvidia / Intel?**

### **Best Answer (customized):**

#### **Qualcomm**

“I want to work on high-performance, low-power SoCs used in billions of devices.
Qualcomm’s focus on mobile, AI accelerators, and modem SoCs is the perfect environment to grow in PD, power optimization, and sign-off.”

#### **Nvidia**

“I want to work on cutting-edge GPU architecture, massive compute tiles, and clock meshes.
Nvidia’s work in accelerated computing, AI, and HPC aligns directly with my GPU PD experience.”

#### **Intel**

“Intel’s focus on advanced process nodes (Intel 3/Intel 20A), backside power delivery, and large compute SoCs is ideal for my interest in timing/IR closure and full-chip PD.”

---

### **HR Question:**

**What is the most difficult bug you solved in PD?**

### **Best Answer:**

“In my GPU PD project, a post-route hold violation appeared only in one fast-corner mode.
I traced it to an over-optimized path created during CTS.
I fixed it by inserting targeted delay buffers and reducing skew through useful-skew adjustment.
This experience strengthened my debugging skills in MCMM timing.”

---

### **HR Question:**

**Why should we hire you?**

### **Best Answer:**

“I bring strong hands-on physical design experience — floorplan, placement, CTS, routing, timing closure, sign-off, IR/EM analysis, and automation.
I can debug issues quickly, communicate clearly, and deliver under deadlines.
My GPU PD and RISC processor RTL-to-GDS experience show I can contribute from day one.”

---

# ✅ **PART 4 — FULL MOCK INTERVIEW (You answer; I give feedback)**

Here is a **15-question REAL PD interview simulation** (Qualcomm/Nvidia style).
Reply with your answers, and I’ll evaluate them like an interviewer.

---

### **MOCK INTERVIEW – START**

1. Explain your block-level floorplanning strategy.
2. What were the main timing bottlenecks in your GPU tile project?
3. How do you debug a sudden local congestion hotspot?
4. What is IR-aware placement?
5. How do you check clock tree health after CTS?
6. What causes hold violations at fast corners?
7. Explain your approach to fixing crosstalk timing violations.
8. How do you reduce dynamic IR drop?
9. What is the difference between RC extraction before and after metal fill?
10. Explain useful skew with an example.
11. How do you decide which nets need NDR?
12. What is glitch power and how do you reduce it?
13. What is the impact of scan chain reordering?
14. How do you perform a sign-off quality check before GDS?
15. Why should we select you for a PD engineer role?

---


