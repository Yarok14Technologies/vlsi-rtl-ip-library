## Next: 45-minute mock interview simulation (you ask, I answer, you grade)

Ready when you are — here's how we’ll run it so it's highest value:

**Format**

* You ask a question (or a short series), time it as you prefer.
* I will answer concisely as if in an actual interview (structured, with trade-offs and commands/code where relevant).
* After each answer you can grade (use the rubric below) and optionally ask follow-ups.
* I’ll give brief feedback on how to improve the answer.

**Grading rubric (use this to grade my answers):**

* Correctness (0–5)
* Depth (0–5)
* Practicality / Actionability (0–5)
* Communication (0–5)
  Total out of 20. Target for top-tier companies: 17–20.

If you want, I can *timebox*: I’ll answer each question in ~90–120 seconds; indicate “Next” to prompt your next question. But I won’t enforce timing — you run it.

Start by asking your first interview question whenever ready, and I’ll answer like a candidate in an onsite interview.

---

## Expanded write-up: **Scan Insertion + Test-Mode SDC — Full Guide (with diagram)**

Below is a focused, interview-grade deep-dive into **scan insertion** and **test-mode SDC**: what to do, why it matters, common pitfalls, and a practical example. I included the small scan-chain diagram you can download above.

### 1) Goal

Insert scan into RTL/netlist to make internal flip-flops controllable/ observable by ATPG, and provide SDC constraints for test clocks (shift/capture) so STA and ATPG operate correctly.

### 2) Why it matters

* Scan drastically reduces ATPG complexity by converting sequential testing into controllable combinational problems.
* Proper SDC prevents misinterpreting test-only timing as functional timing (reduces false failures).
* Physical placement and chain ordering impact shift timing, routing congestion, and manufacturability.

### 3) Steps (high-level)

1. **Prepare RTL/netlist**: identify non-scanable elements (asynchronous FFs, latches, memories).
2. **Decide scan type**: multiplexed (common) vs. latch-based vs. partial-scan. Multiplexed preserves functional timing more easily when using vendor scan cells.
3. **Define scan pins**: TCK/TMS/TDI/TDO or `tclk`, `se`, `scan_in`, `scan_out`. Choose per board/JTAG convention.
4. **Run pre-DFT DRC**: find unsupported cells, clock gating without test bypass, asynchronous resets, X-sources.
5. **Insert scan**: use vendor tool (Design Compiler DFTMAX, Cadence Genus/Innovus DFT flows, or Mentor Tessent). Balance chains (equal lengths) or specify custom ordering.
6. **Export scanned netlist** and generate `test_mode.sdc`.
7. **Run shift-mode STA** (set operating mode to shift) to verify hold across chains.
8. **Run capture-mode STA** (normal functional timing; ensure scan muxing doesn't break setup).
9. **ATPG**: run stuck-at (and transition) ATPG, review coverage; add test points if coverage low.
10. **Physical-aware fixes**: change chain order, split chains, insert hold buffers, or adjust placement.

### 4) SDC essentials for test (what to include)

* **create_clock** for shift clock (TCK) and capture (functional) clock.
* **set_clock_groups -asynchronous** to avoid reconvergence pessimism between shift & capture clocks.
* **set_false_path** between scan chain internal nets so functional STA ignores scan-only nets.
* **set_disable_timing** for SE control nets so tools don't try to time them.
* **multicycle constraints** for intentionally multi-cycle capture paths (if any).
* **test-mode operating mode** (some tools let you set `set_operating_mode shift`).

Example (see downloaded `test_mode.sdc`) — create shift_clk, capture_clk, disable timing across SE, false paths for scan nets.

### 5) Physical considerations & common fixes

* **Hold failures during shift**: caused by very short paths between consecutive scan FFs. Fixes:

  * Insert small hold buffers on chain nets (physical insertion), or
  * Re-order chain to separate problematic FF pairs, or
  * Slight slowdown of shift clock (if board supports).
* **Routing congestion**: long chains that snake across macros cause routing pressure — split into multiple chains per region and compress patterns on-chip.
* **Power/IR during capture**: capture toggling can cause IR drop; add capture power limits and use low-power ATPG modes.
* **Clock gating**: ensure gating cells have test bypass; SE must reach all FFs reliably.

### 6) ATPG considerations tied to scan

* X-sources (tri-states, async resets) must be fixed or masked. Provide an X-list to ATPG.
* Memory and MBIST: exclude array internals from scan ATPG; test via MBIST.
* Compression: plan on-chip decompression to reduce pattern count and ATE time.

### 7) Example flow commands (tool-agnostic)

* Insert scan: `dft_insert -scan -scan_cell scandff -chain_balance auto` (vendor-specific)
* Export SDC: `write_sdc test_mode.sdc`
* Shift-mode STA: `set_operating_mode shift; update_timing; report_timing -max_paths 20`
* ATPG: `run_atpg -model stuck_at -out patterns.stil; report_coverage > cov.txt`

### 8) Interview talking points (concise bullets)

* "Scan converts sequential testing to combinational by using scan chains — enabling deterministic ATPG."
* "SDC must declare shift vs capture clocks and disable timing on scan-only nets to avoid false STA failures."
* "Physical-aware chain ordering is critical — aim to localize chains, minimize routing & fix hold via buffer insertion."
* "MBIST handles memories; scan handles logic — coordinate their patterns and repair flows."

---

If you want, I can now:

1. Start the 45-minute mock interview (you ask first question).
2. Or run a *simulated* 10-question interview where I both ask and answer, then grade — but you asked to ask me and grade, so I’ll wait for your first question.

Which do you want? Start by asking your first interview question and I’ll answer.
