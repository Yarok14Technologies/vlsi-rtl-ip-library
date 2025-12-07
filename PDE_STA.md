# **🚀 200 Super-Advanced PD + STA Questions (5 nm / 3 nm Focused)**

---

# **SECTION 1 — STA: Setup/Hold, CRPR, AOCV/POCV, LVF (40 Q)**

1. Explain mathematically how setup/hold checks differ under AOCV vs POCV.
2. How are correlation coefficients (ρ) used in POCV variance calculations?
3. Derive effective sigma for a path with 12 stages under LVF-based timing.
4. How does CRPR compute pessimism reduction for multi-level reconvergence?
5. What is the limitation of CRPR in case of multi-clock domain reconvergence?
6. Why do hold margins collapse in advanced nodes despite strong CTS?
7. Give a case where CRPR *increases* pessimism.
8. Explain how PVT corners affect delay sensitivity at 5 nm vs 16 nm.
9. Why is LVF required for EUV nodes?
10. How to choose derating factors for a new process with unknown sigma?
11. Difference between cell delay variability vs interconnect variability.
12. Explain impact of temperature inversion on setup checks.
13. Why do slow corners sometimes show *better* timing at <5 nm?
14. How to evaluate path criticality using slack sigma ratio?
15. Give examples where POCV produces worse results than AOCV.
16. Why does advanced-node STA require waveform propagation?
17. Explain how current source models (CCS) affect STA accuracy.
18. What is edge rate pushout and how does it affect timing?
19. Purpose of composite current source (CCSmax/CCSmin) libraries.
20. Why does derate stacking cause over-margining?
21. Explain pros/cons of removing OCV guards altogether.
22. How does multi-voltage STA complicate OCV/POCV?
23. Why is clock slew critical in 3 nm designs?
24. How to analyze timing under dynamic voltage droop?
25. Explain the use of ECO-based split corners.
26. How does multi-driver reconvergence impact CRPR?
27. When should CRPR be disabled?
28. How to compute timing window (Twindow) for aggressor analysis?
29. Crosstalk filtering: how STA eliminates false aggressors.
30. Explain graph-based vs path-based STA divergence.
31. Why path-based STA is mandatory in near-threshold designs.
32. How to quantify pessimism in path-based vs graph-based timing.
33. How high fanout affects stage-based derating.
34. Relationship between LVF and machine-learning based STA.
35. Why STA pessimism grows exponentially with deeper cones.
36. Does crosstalk affect hold timing? Explain edge alignment rules.
37. Formula for total pessimism = derate + variability + CRPR loss.
38. How MMMC interacts with LVF tables.
39. Why late mode tends to produce more pessimistic skew at 3 nm.
40. Best way to detect hidden timing loops early.

---

# **SECTION 2 — CTS/Clocking/Skew/Mesh (30 Q)**

41. How is clock mesh skew modeled under on-chip variation?
42. Why hybrid tree–mesh is better for GPU core tiles?
43. Explain sensitivity of skew to metal thickness variation.
44. When would you avoid using mesh clocking?
45. Why do clock cells degrade more under IR drop?
46. How useful skew interacts with hold corners.
47. Why useful skew becomes harder in deeper pipelines.
48. Compute skew variation across 4 PVTs for 3-level tree.
49. What causes mesh hot-spots in EUV nodes?
50. Why clock gate placement affects timing even post-CTS.
51. How to build a low-power clock tree for a high-frequency tile.
52. Explain multi-source CTS with examples.
53. Why clock buffers use non-default rules (NDR).
54. How crosstalk on clock nets behaves differently from data nets.
55. Why duty-cycle distortion grows after CTS.
56. How to account for pulse-width checks in multi-corner flows.
57. Clock uncertainty breakdown: jitter + skew + latency.
58. Why clock jitter dominates at 5 nm.
59. How PLL phase noise maps into timing margins.
60. Explain early/late clock balance optimization.
61. Why MIM caps are placed near clock roots.
62. What is clock-data compensation?
63. Explain clock GFM (global frequency mesh).
64. Why register clustering improves CTS.
65. Why clock splitters must avoid OD undersize corners.
66. How to ensure low IR drop in local clock grids.
67. Modeling of clock gate wake-up timing.
68. Why mesh CTS requires special routing layers.
69. How to build timing ECO buffers that don’t break skew.

---

# **SECTION 3 — Placement, Congestion, Density, Algorithms (25 Q)**

70. Why advanced-node placement is congestion-first, not timing-first.
71. What is layer-aware placement?
72. How via blockage density affects timing closure.
73. Why Euclidean distance no longer works for placement estimations.
74. How machine-learning improves modern placers.
75. Why GPU-tile placement differs from CPU core placement.
76. How to predict congestion before routing.
77. Explain routability score (RS) calculation.
78. Why pin-access is the #1 problem in 5 nm.
79. Why double-back rows are used in dense blocks.
80. Explain alternating-cell-orientation and its QoR impact.
81. How diffusion breaks affect post-route optimization.
82. How to reduce pin density near macro edges.
83. When to use fence regions for hard blocks.
84. Why placement halos are corner–dependent.
85. Routing demand = cell pin density × layer availability — explain.
86. Multi-bit flops effect on local congestion.
87. Why register cloning helps congestion.
88. Explain RL-based global placement algorithms.
89. How power-switch cell placement affects IR.
90. Why legalizer failures occur in advanced nodes.
91. What is spare-cell congestion?
92. Explain clock-region aware placement.
93. Why row height variation impacts RC.
94. Calculate expected congestion for a macro-channel design.

---

# **SECTION 4 — Routing, DRC, DFM, Litho, EUV (35 Q)**

95. Why RC variation in M0–M2 layers dominates delay at 5 nm.
96. How self-aligned double patterning affects routing grids.
97. Explain track reservation for critical nets.
98. What is via pillar and why essential in dense blocks?
99. Why M2/M3 min-area rules blow up congestion.
100. Difference between EUV overlay vs DP overlay.
101. Why SADP enforces directionally-locked routing.
102. How pattern matching rules restrict routing topology.
103. What is forbidden-pitch violation?
104. Why wide wires may break multi-patterning.
105. Line-edge roughness (LER) impact on delay.
106. Why EUV does not eliminate multi-patterning entirely.
107. How to reduce min-cut violation hotspots.
108. What is via farm collapse?
109. Why jog alignment rules explode in 5 nm.
110. How to reduce metal density mismatch.
111. Why cut-nets are timing-critical in GPU blocks.
112. What is EUV stochastic failure?
113. Why DRC after ECO can create antenna violations.
114. Explain timing-driven routing vs detour routing.
115. How coupling cap extraction changes at 3 nm.
116. Why pattern-based DRC is non-local.
117. How to fix path-based antenna under tight spacing.
118. Why HR (hierarchical routing) collapses sometimes.
119. How IR-aware routing works.
120. What is electromigration-aware via selection?
121. How to avoid bridging defects in EUV layers.
122. Why local interconnect layers dominate hold timing.
123. DFM hotspot scoring algorithm.
124. What is rotating cell rows doing for routing?
125. How to fix unidirectional routing conflicts.

---

# **SECTION 5 — Power, IR Drop, EM, Thermal (20 Q)**

126. Why IR drop is more timing-critical at lower Vdd.
127. How to compute effective IR drop from dynamic workloads.
128. Why decap effectiveness drops at 5 nm.
129. How EM rules change for finFET vs planar nodes.
130. How to reduce IR drop near compute clusters.
131. How clock mesh increases IR drop.
132. Why local IR hotspots occur near ALUs.
133. How via EM reliability improves with parallel via stacks.
134. Explain reliability modeling for aging (BTI/HCI).
135. Dynamic IR-aware STA — how to integrate.
136. Why thermal coupling increases delay variability.
137. Why on-chip thermal sensors are mandatory.
138. How bump-map changes IR profile.
139. Why MIM caps must be near clock roots.
140. Explain power gating wake-up timing.
141. How to compute EM lifetime using Black’s equation.
142. Why narrow metal width accelerates EM failures.
143. Explain decap refill time constants.
144. Why IR drop at the capture flop matters more.

---

# **SECTION 6 — ECO & Sign-off Closure (20 Q)**

145. Why metal-only ECO becomes hard in advanced nodes.
146. How to decide ECO buffer insertion location algorithmically.
147. Explain bypass routing for ECO.
148. How ECO interacts with MCMM streams.
149. Why ECO in congested regions risks DRC explosions.
150. How to avoid hold ECO breaking setup in other corners.
151. How to preserve shielding during ECO.
152. Why bumping cell Vt for ECO can break leakage budget.
153. Explain path perturbation due to ECO re-routing.
154. Physical-only vs logical-only ECO.
155. Why STA after ECO must use graph-based + PBA hybrid.
156. How to use “ECO-friendly cells” in design.
157. Why ECO can disturb mesh balance.
158. How to ensure ECO timing fixes are deterministic.
159. How to automate 50-path ECO generation.
160. Why antenna re-fixes are common after ECO.
161. How to run selective extraction for ECO nets.
162. Why ECO can cause pattern-matching failures.
163. How to freeze DRC hotspots before routing ECO.
164. When to use non-buffer ECO (Vt-swap / downsizing).

---

# **SECTION 7 — Synthesis–to–PD–to–Signoff Integration (20 Q)**

165. How to ensure synthesis constraints match PD SDC.
166. Why retiming interacts with PD in unexpected ways.
167. How floorplan assumptions must be fed back into synthesis.
168. Why wireload models are useless at 5 nm.
169. Best way to generate placement constraints from RTL structure.
170. How to ensure logic equivalence after PD ECO.
171. How scan optimization interacts with timing.
172. Why false-path modeling becomes non-local.
173. How to debug missing mode/corner coverage.
174. Explain hierarchical vs flat STA trade-offs.
175. Why interface timing is always hardest in large SoCs.
176. How to keep constraints clean during mode proliferation.
177. Why power-intent (UPF) affects timing windows.
178. What is dynamic mode-switch timing?
179. How to reduce pessimism in hierarchical timing.
180. Why cross-boundary congestion dominates runtime.
181. How to fix "flop clustering mismatch" between synthesis and PD.
182. Why black-boxing causes incorrect STA.
183. How to isolate timing loops across hierarchy.
184. How partial block sign-off works.

---

# **SECTION 8 — GPU/CPU/SoC Architecture + PD Integration (20 Q)**

185. Why GPU tiles have worst congestion vs CPU tiles.
186. How to plan PD for thousands of repeated compute units.
187. Why vector-processing blocks create IR hotspots.
188. How NoC routing affects timing closure.
189. How to place L2/L3 cache macros efficiently.
190. Why pipeline depth affects CTS architecture.
191. Explain PD challenges in systolic arrays.
192. Why ALU clusters cause temperature gradients.
193. How warp schedulers influence placement constraints.
194. How tensor cores increase routing complexity.
195. Explain clock mesh partitioning in GPU sub-blocks.
196. Why multi-die 2.5D integration complicates STA.
197. How local interposer RC affects timing paths.
198. Why GPUs need very flat hierarchy for PD.
199. Why scan stitching is hard in GPU tiles.
200. How to handle timing for highly replicated SIMD blocks.

---

