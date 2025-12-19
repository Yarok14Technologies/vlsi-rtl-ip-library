Below is a **clean, interview-ready explanation of UVM fundamentals**, exactly the way **Qualcomm / NVIDIA / Staff-level DV** panels expect. I’ll keep it precise and technical.

---

## 1️⃣ `create()` vs `new()` in UVM

### 🔹 `new()`

* **SystemVerilog constructor**
* Used for **non-UVM objects**
* No factory support
* No override capability

```systemverilog
class my_obj;
  function new(string name="my_obj");
  endfunction
endclass

my_obj o = new("o");
```

### 🔹 `create()`

* **UVM factory-based creation**
* Supports **type override / instance override**
* Required for **all UVM components & sequence items**

```systemverilog
my_driver drv;
drv = my_driver::type_id::create("drv", this);
```

### 🔑 Key Differences (Interview Table)

| Aspect            | `new()`          | `create()`                     |
| ----------------- | ---------------- | ------------------------------ |
| Factory support   | ❌ No             | ✅ Yes                          |
| Override possible | ❌ No             | ✅ Yes                          |
| Hierarchy aware   | ❌ No             | ✅ Yes                          |
| Used for          | Plain SV objects | UVM components, sequence items |
| Parent-child link | ❌                | ✅                              |

📌 **Rule:**

> ❗ All `uvm_component` and `uvm_object` derivatives → **must use `create()`**

---

## 2️⃣ Driver–Sequencer Handshake (HS) Communication

### 🔹 Core Mechanism

UVM uses **TLM FIFO-like handshake** between sequencer and driver.

```
Sequence → Sequencer ⇄ Driver → DUT
```

### 🔹 Ports Used

* **Sequencer → Driver**

  * `uvm_seq_item_pull_port`
* **Driver → Sequencer**

  * `uvm_seq_item_pull_imp`

### 🔹 Typical Driver Code

```systemverilog
class my_driver extends uvm_driver #(my_txn);

  task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);   // BLOCKING HS
      drive_to_dut(req);
      seq_item_port.item_done();           // ACK
    end
  endtask

endclass
```

### 🔹 What Happens Internally

1. Sequence calls `start()`
2. Sequencer arbitrates sequences
3. Driver calls `get_next_item()`
4. Transaction transferred
5. Driver calls `item_done()`
6. Sequencer releases lock

### 🔑 Interview Keywords

* **Blocking handshake**
* **Back-pressure**
* **Arbitration**
* **Lock / Grab**
* **Transaction ownership**

---

## 3️⃣ UVM Testbench Phases & Components

### 🔹 UVM Component Hierarchy

```
uvm_test
 └── uvm_env
      ├── uvm_agent
      │    ├── uvm_sequencer
      │    ├── uvm_driver
      │    └── uvm_monitor
      ├── uvm_scoreboard
      └── uvm_coverage
```

---

## 4️⃣ UVM Phases (MOST ASKED)

### 🧱 Build & Setup Phases (STATIC)

| Phase                 | Purpose                         |
| --------------------- | ------------------------------- |
| `build_phase`         | Create components using factory |
| `connect_phase`       | Connect TLM ports               |
| `end_of_elaboration`  | Topology checks                 |
| `start_of_simulation` | Print config, banners           |

📌 **No time consumed**

---

### ⏱️ Run-Time Phases (DYNAMIC)

| Phase             | Purpose           |
| ----------------- | ----------------- |
| `run_phase`       | Main stimulus     |
| `reset_phase`     | DUT reset         |
| `configure_phase` | Program registers |
| `main_phase`      | Normal operation  |
| `shutdown_phase`  | Graceful stop     |

📌 **Consumes simulation time**

---

### 🧹 Cleanup Phases

| Phase           | Purpose                    |
| --------------- | -------------------------- |
| `extract_phase` | Collect results            |
| `check_phase`   | Compare expected vs actual |
| `report_phase`  | Print summary              |
| `final_phase`   | End simulation             |

---

## 5️⃣ Very Common Interview Traps (Be Ready)

### ❓ Why not `new()` for components?

➡ Breaks **factory override**, **hierarchy**, **config_db**

### ❓ Can driver talk directly to sequence?

➡ ❌ No, **only via sequencer**

### ❓ Can multiple sequences run?

➡ ✅ Yes, sequencer **arbitrates**

### ❓ Where to raise objections?

➡ `run_phase` (or sub-phases)

```systemverilog
phase.raise_objection(this);
...
phase.drop_objection(this);
```

---

## 6️⃣ One-Line Staff-Level Summary

> “UVM uses factory-controlled object creation, phase-synchronized execution, and sequencer-driver handshake via TLM to ensure reusable, scalable, and override-friendly verification environments.”

---

