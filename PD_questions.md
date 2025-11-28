Here are **Physical Design Engineer (PDE)** interview questions—these are REAL questions asked in **Qualcomm, NVIDIA, Intel, AMD, Broadcom, MediaTek, and Apple** for physical design (PnR + STA + signoff) roles.

I’ve separated them into difficulty levels + domains so you can prepare like a professional.

---

# 🟦 **BASIC PHYSICAL DESIGN (PnR) QUESTIONS**

### 1. What are the steps in a typical **physical design flow**?

* Synthesis
* Floorplanning
* Power planning
* Placement
* CTS
* Routing
* STA
* Signoff (DRC/LVS)

### 2. Explain **core utilization**.

### 3. What is the difference between **core area** and **die area**?

### 4. What is **aspect ratio** in floorplanning?

### 5. What is a **macro** and a **soft block**?

### 6. Why do we need **tap cells** and **endcap cells**?

### 7. What are **tie-high** and **tie-low** cells?

### 8. Difference between **pre-CTS** and **post-CTS** optimization.

### 9. Why is routing done in multiple layers?

### 10. What is **congestion** and how do you reduce it?

---

# 🟩 **FLOORPLANNING QUESTIONS**

### 11. What factors decide macro placement?

### 12. What is the halo around macros?

### 13. What are **blockages** (soft, hard, partial)?

### 14. How do you fix **pin accessibility issues**?

### 15. What is a **power strap** and how do you decide strap width/spacing?

### 16. Explain **IR drop** and fixes (power grid strengthening, decaps).

### 17. What is the purpose of **decap cells**?

### 18. What is **antenna effect** and how to fix it?

### 19. Explain **CTS balancing logic**.

### 20. How do you create a **clock mesh** vs. **clock tree**?

---

# 🟧 **PLACEMENT & CTS QUESTIONS**

### 21. What is **legalization** after placement?

### 22. What is **cell spreading**?

### 23. How do you minimize **routing congestion** during placement?

### 24. Define **skew**, **latency**, and **uncertainty**.

### 25. Why do we do **pre-CTS optimizations**?

### 26. What is **useful skew**?

### 27. Explain **H-tree** clock distribution.

### 28. What causes **clock divergence**?

### 29. How do you optimize high-fanout nets?

### 30. How do you fix **clock gating timing violations**?

---

# 🟥 **ROUTING QUESTIONS**

### 31. Explain **global routing** vs **detailed routing**.

### 32. What is **DRC**?

### 33. What is **min spacing**, **min width**, **notch**, **via enclosure**?

### 34. What are **cut layers**?

### 35. What is **wire resistance vs capacitance** impact on timing?

### 36. Why are upper layers thicker?

### 37. How do you minimize **crosstalk** during routing?

### 38. Explain **shielding** and **double-width routing**.

### 39. What is **timing-driven routing**?

### 40. What causes via failures and how to avoid them?

---

# 🟪 **STATIC TIMING ANALYSIS (STA) QUESTIONS**

### 41. Define **setup violation** and how to fix it.

### 42. Define **hold violation** and how to fix it.

### 43. Explain **setup equation** and **hold equation**.

### 44. What is **OCV**, **AOCV**, **POCV**?

### 45. What is **PVT corner**?

### 46. What is **clock reconvergence pessimism** (CRP)?

### 47. How do you apply **multi-cycle path constraints**?

### 48. What is a **false path**?

### 49. Explain **data-to-data** and **clock-to-clock paths**.

### 50. How do you fix negative slack in post-route STA?

---

# 🟫 **SIGNOFF QUESTIONS (DRC, LVS, EM/IR)**

### 51. Difference between **DRC** and **LVS**.

### 52. What is **ERC**?

### 53. Explain **EM (Electromigration)** — causes & prevention.

### 54. What is **IR drop**? Static vs dynamic.

### 55. What is **voltage droop**?

### 56. How do decap cells reduce IR drop?

### 57. What causes **LVS mismatches**?

### 58. What are **antenna violations**? Fixes?

### 59. What is **dummy metal filling**?

### 60. What is **density rule** in manufacturing?

---

# 🔥 **ADVANCED PDE QUESTIONS (Asked at NVIDIA / Google TPU / Apple)**

### 61. How do you close timing on a critical long path that fails across multiple corners?

### 62. How do you handle **multi-Vt optimization**?

### 63. Explain **clock tree robustness** under variation.

### 64. What is the difference between **mesh**, **H-tree**, **spine**, and **hybrid** clocks?

### 65. How do high-frequency chips reduce jitter?

### 66. What is **CTS clustering**?

### 67. Explain **RC extraction** types:

* C-only
* RC
* Asymmetric RC

### 68. How do you reduce power in physical design?

* Clock gating
* Multi-Vt
* Low-power libraries
* Power gating
* Switched power domains

### 69. Discuss timing challenges in **7nm/5nm FinFET** nodes.

### 70. What is **double patterning** and **EUV**?

---

# 🧠 **Scenario-Based PDE Questions (most important!)**

### 71. Your design fails hold in FF corner after routing — what do you do?

### 72. Congestion at macro corners — fixes?

### 73. IR drop is high in a local region — what steps will you take?

### 74. Clock skew is too high in a sub-block — fixes?

### 75. Setup is clean but hold is failing badly — root cause?

### 76. Memory macro has inaccessible pins — how do you fix it?

### 77. Routing DRCs explode after CTS — why?

### 78. Clock gating cells cause glitches — how to solve?

### 79. Too many vias on one net — how to optimize?

### 80. Metal density violations — how do you fix?

---

# 🟧 **TOOLS QUESTIONS (Cadence, Synopsys, OpenROAD/OpenLane)**

### Cadence Innovus questions:

81. What is `place_opt` vs `optDesign`?
82. What is `setOptMode` used for?
83. What is `ctsSpec`?
84. What is `optDesign -postRoute`?
85. Explain `timeDesign -signoff`.

### Synopsys ICC2 questions:

86. Difference between Fusion Compiler and ICC2?
87. What is `clock_opt`?
88. What is `route_auto`?
89. What is `check_design`?

### OpenRoad/OpenLane (if using Sky130):

90. What is `pdngen`?
91. How do you adjust utilization in OpenLane?
92. How to generate SDC for multi-clock?
93. What is `repair_timing`?
94. What is `dpl` (detail placement)?
95. Explain OpenSTA basic flow.

---

