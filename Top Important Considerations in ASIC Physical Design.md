

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
