

# ⭐ **Top Important Considerations in ASIC Physical Design**

![Image](https://blogger.googleusercontent.com/img/b/R29vZ2xl/AVvXsEgJ6LLqgIhCoJGWFmwFwlZZcq8yPnyzjeIFUwrOEOUtFiQXo0l0ZAGgBSvuijwe2A7JDiguACGjYIYuUWub-Vi9X5jSt_ZfR7Y__bISY_77U9e8nBccQ71nuG1iak2CV2UBcOKUAKzAs6il/s1600/Screenshot%2B%252823%2529.png?utm_source=chatgpt.com)

![Image](https://blogger.googleusercontent.com/img/b/R29vZ2xl/AVvXsEjHRxm97pQ7507S1zmn06RJbnvOziy3vAL8EP4jPIRU84N-KKhGD6U_UVRw8ELcgx7LLy3hLYCvSziq4O0ESsvji9oFxty61TyA2jIQKmx3MA0vyazT6Wkwsd486rnNTy8AUFwZ_XeeGNzf/s640/placement1.PNG?utm_source=chatgpt.com)

![Image](https://www.researchgate.net/publication/329079777/figure/fig1/AS%3A695210430431234%401542762491634/Domains-in-the-chip-floorplan.png?utm_source=chatgpt.com)

---

# 1️⃣ **Floorplanning (FP) – The Foundation**

### **Goals:** Optimal area, best timing, minimal congestion, clean power.

### **Must-Check Points**

* **Aspect ratio & core utilisation**

  * Start with 60–70% utilisation (digital blocks).
  * Too high → congestion; too low → wasted area.
* **Macro placement**

  * Place **large macros at the periphery**.
  * Maintain *halos/keepouts* for routing.
  * Analog blocks → isolate from noisy digital blocks.
* **Pin placement**

  * Place IO pins closest to relevant logic.
  * Reduce long cross-die nets.
* **Power planning**

  * Use rings + stripes.
  * Ensure **uniform metal coverage**.
  * Place **power switches** logically if using power gating.
* **Clock distribution planning**

  * Keep clock regions balanced.
  * Uniform CTS buffer regions.
* **Channel spacing**

  * Leave routing channels near macros.

---

# 2️⃣ **Placement (PL) – Logic Positioning**

### **Goals:** Minimize wirelength, congestion, timing violations.

### **Critical Considerations**

* **Timing-driven placement**

  * Prioritize cells on critical paths → cluster closer.
* **Congestion analysis**

  * Repair congested regions → cell spreading / macro shift.
* **Cell density targets**

  * Hotspots must be < 75% density.
* **Legalization**

  * Ensure no overlaps, DRC violations.
* **Use multi-bit flops (MBFF)**

  * Saves area & power.
* **Buffer proliferation**

  * Avoid too many buffers → indicates long paths.

---

# 3️⃣ **Clock Tree Synthesis (CTS)**

### **Goals:** Minimum skew + balanced clock insertion delay.

### **Must-Check Points**

* **Clock skew < 5–10% of clock period**
* **Minimize clock latency**
* **Use H-tree / fishbone / mesh depending on chip**
* **Shield clock nets**

  * Avoid coupling noise.
* **Useful skew**

  * Introduce skew to fix setup/hold.

---

# 4️⃣ **Routing (RT) – Building Interconnect**

### **Goals:** DRC clean, minimal RC delay, reduced congestion.

### **Important Points**

* **Global routing check**

  * Ensure < 1% overflow.
* **Track assignment**

  * Horizontal/vertical layers use recommended metals.
* **Signal integrity**

  * Crosstalk reduction: spacing, shielding.
* **DRC clean routing**

  * Via rules, min spacing, minimum enclosure.
* **Antenna correction**

  * Insert antenna diodes where necessary.
* **RC extraction accuracy**

  * Accurate parasitics → accurate STA.

---

# 5️⃣ **PVT (Process–Voltage–Temperature) Corners**

### **Goals:** Ensure the chip works in all worst-case corners.

### **You Must Analyse:**

* **Setup check @ Slow–Slow (SS), low V, high T**
* **Hold check @ Fast–Fast (FF), high V, low T**
* **Power analysis @ Typical (TT) and FF**
* **Leakage @ high temperature**
* **IR-drop under min/max voltage**

### **Don’t forget:**

* **OD/OCV/AOCV/POCV**

  * For deep-submicron timing accuracy.
* **Noise corners**

  * crosstalk, jitter.

---

# 6️⃣ **Timing (STA) – Setup, Hold, DRV**

### **Critical Items**

* **Setup violations**

  * Fix by: upsizing, buffering, reducing wirelength, useful skew.
* **Hold violations**

  * Fix by: buffer insertion, downsizing, path delay increase.
* **Clock uncertainties**

  * Jitter + PVT + OCV margins.
* **False & multi-cycle paths**

  * Must be cleanly defined.

---

# 7️⃣ **Power Integrity (IR Drop, EM)**

### **Goals:** Stable power to every cell.

### **Checklist**

* **Static IR-drop** < 5% recommended
* **Dynamic IR-drop** < 10% recommended
* **EM (Electromigration)**

  * Fix with widening wires, extra vias.
* **Decap insertion**

  * Especially near clock regions and macros.
* **Power grid density**

  * Must meet tool guidance.

---

# 8️⃣ **Signal Integrity (SI)**

### **Considerations**

* **Crosstalk delays**
* **Aggressor-victim switching**
* **Shielding critical nets**
* **Clock nets require stronger SI protection**

---

# 9️⃣ **DFT Considerations**

### **DFT Must Be Planned Early**

* Scan chain reordering post-placement.
* Avoid long scan routes.
* Ensure no congestion created by scan stitching.
* JTAG TAP accessibility.

---

# 🔟 **Physical Verification**

### **Checklist**

* **LVS clean** (Layout vs Schematic)
* **DRC clean**
* **Antenna checks**
* **ERC** (electrical rule check)

---

# 1️⃣1️⃣ **Mixed-Signal / Custom Blocks (Your Yarok-14 Case)**

### **Special Care**

* Guard rings around ADC/DAC & sensor interfaces.
* Deep N-well for isolation.
* Shield analog routing with VDD/GND.
* Separate analog and digital power domains.
* Clock jitter requirements for DSP section.

---

# ✔ Summary Cheat Sheet

| Stage            | Most Important Factors                                |
| ---------------- | ----------------------------------------------------- |
| **Floorplan**    | Power grid, macro placement, channels, pin placement  |
| **Placement**    | Timing-driven, congestion removal, MBFF, legalization |
| **CTS**          | Low skew, low latency, shielding                      |
| **Routing**      | DRC clean, SI & crosstalk, correct layer usage        |
| **PVT**          | SS for setup, FF for hold, leakage, OCV/AOCV/POCV     |
| **Timing**       | Setup/hold closure, uncertainty modeling              |
| **IR/EM**        | Decaps, wide metals, IR-drop maps                     |
| **Verification** | DRC, LVS, Antenna, ERC                                |
| **Mixed-signal** | Isolation, guard rings, low-noise routing             |

---
**TOP 30 considerations for EACH stage** of ASIC Physical Design: **Floorplanning, Placement, CTS, Routing, PVT, STA, IR/EM, SI, DFT, Physical 

# 🟥 **1. FLOORPLANNING – Top 30 Considerations**

1. Core utilization (55–70% start point)
2. Aspect ratio
3. Macro placement strategy
4. Macro orientation (pins facing logic)
5. Keep-out margins (halos)
6. Macro channel spacing
7. IO pin placement planning
8. Power grid ring generation
9. Power strap pitch & width
10. Macro power connectivity
11. Analog/digital domain separation
12. Noise-sensitive region isolation
13. Clock domain partitioning
14. Level shifter placement regions
15. Isolation cells regioning
16. Voltage domain boundaries
17. Floorplan symmetry
18. Congestion hotspots estimation
19. ECO reservation area
20. Spare-cell insertion planning
21. Decap region planning
22. Feedthrough channel planning
23. Top-level hierarchy partitioning
24. Clock gating cell regioning
25. Timing-critical block proximity
26. Placement blockage definitions
27. Routing blockage setup
28. Tap cell spacing strategy
29. Endcap cell insertion strategy
30. Thermal hotspot estimation

---

# 🟧 **2. PLACEMENT – Top 30 Considerations**

1. Timing-driven placement
2. Congestion-driven placement
3. Global placement density targets
4. Local hot-spot cell spreading
5. High-fanout net clustering
6. Critical path clustering
7. Multi-bit flop insertion
8. Useful-skew impact planning
9. Power-driven placement
10. Clock gate and buffer locations
11. Legalization quality
12. Macro-to-cell distance tuning
13. Cell orientation optimization
14. Placement blockages refinement
15. Soft vs. hard constraints
16. ECO space preservation
17. Hold buffer region planning
18. Repeater insertion planning
19. Antenna-prone net shortening
20. Scan chain reordering awareness
21. Clock domain isolation
22. Density checks per region
23. Avoiding routing choke points
24. CTS-friendly cell distribution
25. VDD/VSS rail alignment
26. Pin accessibility constraints
27. Tap cell & endcap distribution
28. IR-drop pre-estimation
29. Thermal-aware placement
30. Placement QoR verification (WNS/TNS/congestion)

---

# 🟨 **3. CLOCK TREE SYNTHESIS (CTS) – Top 30 Considerations**

1. Clock skew target
2. Clock latency target
3. Insertion delay balance
4. Clock gating logic placement
5. Clock mesh vs. tree selection
6. Buffer/inverter-only tree strategy
7. Shielding of clock routes
8. Clock-to-clock skew control
9. Clock domain crossing regions
10. Useful skew insertion
11. Setup/hold balancing
12. Clock max transition control
13. Max capacitance limits
14. Max fan-out per stage
15. NDR (Non-default rules) usage
16. Routing layer selection for clocks
17. Pre-CTS optimization quality
18. Variation tolerance for PVT
19. Jitter margin allocation
20. IR-drop on clock buffers
21. Differential clock handling
22. Generated clocks modeling
23. Multiple frequency domains
24. Clock tree symmetry
25. Metal density control
26. Clock tree ECO strategies
27. Duty cycle correctness
28. Noise injection near analog blocks
29. Hold-aware CTS
30. Clock tree power estimation

---

# 🟩 **4. ROUTING – Top 30 Considerations**

1. Global routing overflow < 1%
2. Track utilization per layer
3. Timing-critical net routing priority
4. Shielding of critical nets
5. Crosstalk (SI) avoidance
6. Via count minimization
7. Via redundancy for EM
8. Antenna ratio compliance
9. Layer assignment (H/V patterns)
10. Long net repeater insertion
11. Differential pair spacing
12. Matching constraints (analog)
13. DRC-clean routing
14. RC extraction accuracy
15. Resistive IR impact
16. EM-safe current density routing
17. Clock NDR constraints
18. Special-net routing for resets
19. Power route reinforcement
20. Routing congestion hotspots fixing
21. Blockage-aware routing
22. Shielding noisy nets
23. Lower metal usage for dense regions
24. Upper metal usage for long nets
25. Layer jog minimization
26. Scan chain routing optimization
27. ECO-friendly routing
28. Multi-corner timing re-check after route
29. Coupling capacitance control
30. Metal density fill constraints

---

# 🟦 **5. PVT CORNER ANALYSIS – Top 30 Considerations**

1. SS corner for setup
2. FF corner for hold
3. TT for power
4. FF-highV-lowT for worst leakage
5. Voltage tolerance ±10%
6. Temperature range -40°C to 125°C
7. OCV modeling
8. AOCV modeling
9. POCV for deep-submicron
10. derate settings correctness
11. IR-drop influence in slow/fast conditions
12. On-chip variation for clocks
13. Voltage droop timing impact
14. Temp inversion in finFET nodes
15. Multi-corner-multi-mode (MCMM) coverage
16. Aging & reliability corners (NBTI, PBTI)
17. Process skew of macros
18. Process skew of memory compilers
19. Random variation modeling
20. Local variation modeling
21. Global variation modeling
22. Crosstalk timing models
23. Jitter & duty cycle distortion
24. Hold margin at low temperature
25. Setup margin at high temperature
26. Leakage estimation accuracy
27. Dynamic power variation
28. STA ECO per-corner validation
29. Corner-specific routing parasitics
30. Worst-case corner selection for signoff

---

# 🟪 **6. STATIC TIMING ANALYSIS (STA) – Top 30 Considerations**

1. Setup checks
2. Hold checks
3. Clock uncertainty modeling
4. Jitter modeling
5. Crosstalk delay impact
6. AOCV tables application
7. Propagation of clocks correctly
8. Generated clocks correctness
9. Multi-cycle path constraints
10. False path constraints
11. Min pulse width checks
12. Clock gating checks
13. Asynchronous domain checks
14. CDC synchronizer modeling
15. Transition constraints
16. Capacitance constraints
17. Slew impact on timing
18. Liberty model corners
19. STA vs. post-route correlation
20. Interconnect RC corner selection
21. Slew propagation accuracy
22. Capture/launch edge correctness
23. Constraints linting
24. DRV checks (max cap, max tran)
25. Scan mode STA
26. ECO timing safety
27. Setup/hold fixing priority
28. Skew-based timing improvement
29. Path-based analysis (PBA)
30. Gate-based analysis (GBA)

---

# 🟫 **7. IR-DROP & EM – Top 30 Considerations**

1. Power grid density
2. Power ring thickness
3. Strap pitch
4. Strap width
5. Drop target (<10% dynamic)
6. Static IR-drop target (<5%)
7. Power via density
8. EM current limits per metal
9. Via EM stress
10. Metal density variation
11. Decap insertion coverage
12. High-switching region reinforcement
13. Clock-tree power spikes
14. Simultaneous switching noise (SSN)
15. Power gating switch sizing
16. Isolation cell leakage impact
17. Rush current situations
18. Block-level IR budgeting
19. Macro-level power routing
20. Voltage droop under PVT
21. Resonance & inductance
22. Package-power model alignment
23. TSV/3D-IC IR impact (if applicable)
24. Aging EM predictions
25. EM-aware routing
26. Gate-level power estimation accuracy
27. Clock-frequency impact on IR
28. Decap vs. leakage tradeoff
29. IR-aware timing closure
30. Final signoff using RedHawk/Totem

---

# 🟫 **8. SIGNAL INTEGRITY (SI) – Top 30 Considerations**

1. Crosstalk noise
2. Crosstalk delay
3. Shielding of critical nets
4. Spacing rules
5. Differential pair matching
6. Victim-aggressor switching patterns
7. RLC interconnect modeling
8. Jitter induced by SI
9. Long parallel routes
10. Clock net SI protection
11. Reset net SI protection
12. Noise on power grid
13. Ground bounce
14. Inductive coupling
15. Capacitive coupling
16. Max coupling capacitance per net
17. Routing layer selection
18. SI-aware STA
19. Timing window analysis
20. Noise-aware ECO fixes
21. Aggressor window reduction
22. Driver upsizing
23. Victim path slack impact
24. Noise-aware library models
25. SI around analog blocks
26. Crosstalk glitch checks
27. Simultaneous switching buffer issues
28. Long bus switching patterns
29. EM & SI interaction
30. Final SI signoff using PrimeTime-SI

---

# 🟫 **9. DFT (Design for Test) – Top 30 Considerations**

1. Scan chain architecture
2. Scan reordering post-placement
3. Avoid long detours in scan routing
4. Scan compression logic placement
5. Test clock tree distribution
6. BIST block integration
7. MBIST–SRAM connectivity
8. TAP controller placement
9. JTAG routing isolation
10. Boundary scan design
11. Test mode timing paths
12. Hold fixing in test mode
13. Clock gating bypass in test
14. Reset behavior in test modes
15. Scan enable timing
16. Multi-power-domain test constraints
17. Test point insertion
18. Test coverage goals (> 99%)
19. Scan chain power
20. Pattern count limit
21. At-speed test strategy
22. OCC (on-chip clock) handling
23. Reducing test routing congestion
24. LFSR/MISR insertion
25. X-propagation reduction
26. Fault model completeness
27. Controllability & observability
28. Analog/mixed-signal test hooks
29. ATPG constraints correctness
30. DFT signoff

---

# 🟫 **10. PHYSICAL VERIFICATION (PV) – Top 30 Considerations**

1. DRC rules meeting
2. LVS match
3. ERC checks
4. Antenna checks
5. Density fill insertion
6. Metal fill spacing
7. Via counts per rule
8. Width/spacing constraints
9. End-of-line rules
10. Multi-patterning compliance
11. FinFET spacing rules
12. Via enclosure rules
13. Well tie spacing
14. Tap cell spacing
15. Diffusion spacing
16. Poly coverage
17. Minimum metal coverage
18. Notch rules
19. Pin alignment
20. Text label correctness
21. Block boundary alignment
22. Analog guard ring correctness
23. LVS exceptions for analog IP
24. Short detection
25. Open net detection
26. Current density rules
27. ESD routing compliance
28. Pad-ring DRC
29. SDF back-annotation correctness
30. Final GDS signoff

---

