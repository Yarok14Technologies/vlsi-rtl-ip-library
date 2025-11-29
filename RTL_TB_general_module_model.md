 Qualcomm, NVIDIA, or any ASIC/SoC company will expect you to **present Verilog RTL and TB in a clean, modular, and reusable structure**.  the **industry-standard skeleton** you can adapt to **any IP block**.

---

# **1. RTL Block Basic Structure**

```verilog
//----------------------------------------------------
// Module: <IP_NAME>
// Author: <Your Name>
// Date  : <DD/MM/YYYY>
// Description: <Brief description of function>
//----------------------------------------------------

`timescale 1ns/1ps
module <ip_name> #(
    parameter WIDTH = 8,       // Example: data width
    parameter DEPTH = 16       // Example: memory depth
)(
    //================================================
    // Clock and Reset
    //================================================
    input  wire                clk,
    input  wire                rst_n,   // Active low reset

    //================================================
    // Inputs
    //================================================
    input  wire                en,      // Enable
    input  wire [WIDTH-1:0]    din,

    //================================================
    // Outputs
    //================================================
    output reg  [WIDTH-1:0]    dout,
    output reg                 valid
);

    //================================================
    // Internal Signals
    //================================================
    reg [WIDTH-1:0] reg1, reg2;

    //================================================
    // Sequential Logic
    //================================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg1  <= '0;
            reg2  <= '0;
            dout  <= '0;
            valid <= 1'b0;
        end else if (en) begin
            reg1  <= din;
            reg2  <= reg1;
            dout  <= reg2;
            valid <= 1'b1;
        end else begin
            valid <= 1'b0;
        end
    end

endmodule
```

✅ **Key RTL best practices:**

* Always **parameterize widths/depths**.
* **clk & rst_n** should always be first ports.
* Separate **combinational vs sequential always blocks**.
* Use **nonblocking (`<=`)** in sequential, **blocking (`=`)** in combinational.
* Reset logic must be **deterministic**.
* Avoid `initial` in synthesizable RTL.

---

# **2. Testbench Basic Structure**

```verilog
//----------------------------------------------------
// Testbench: <IP_NAME>_tb
// Author   : <Your Name>
// Date     : <DD/MM/YYYY>
// Description: TB for <IP_NAME>
//----------------------------------------------------

`timescale 1ns/1ps
module tb_<ip_name>;

    //================================================
    // Parameters (match DUT)
    //================================================
    parameter WIDTH = 8;
    parameter DEPTH = 16;

    //================================================
    // DUT Ports
    //================================================
    reg                  clk;
    reg                  rst_n;
    reg                  en;
    reg  [WIDTH-1:0]     din;
    wire [WIDTH-1:0]     dout;
    wire                 valid;

    //================================================
    // DUT Instantiation
    //================================================
    <ip_name> #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .din(din),
        .dout(dout),
        .valid(valid)
    );

    //================================================
    // Clock Generation
    //================================================
    initial clk = 0;
    always #5 clk = ~clk;  // 100 MHz

    //================================================
    // Stimulus
    //================================================
    initial begin
        // Initialize
        rst_n = 0; en = 0; din = '0;
        #20 rst_n = 1;

        // Apply stimulus
        repeat (5) begin
            @(posedge clk);
            en  = 1;
            din = $random;
        end

        @(posedge clk);
        en = 0;

        #50 $finish;
    end

    //================================================
    // Monitor
    //================================================
    initial begin
        $display("Time\tclk\trst_n\ten\tdin\tdout\tvalid");
        $monitor("%0t\t%b\t%b\t%b\t%h\t%h\t%b",
                  $time, clk, rst_n, en, din, dout, valid);
    end

endmodule
```

✅ **Key TB best practices:**

* **Self-checking**: compare `dout` with expected model (not shown in skeleton).
* **Clock/Reset generation** is always included.
* Use `$monitor`/`$display` for debugging.
* Use `repeat`, `fork-join`, or tasks to structure testcases.
* Keep TB **untimed where possible**, rely on clock edges (`@(posedge clk)`).

---

# **3. Typical File Organization**

```
/rtl
   ip_name.v
   fifo.v
   alu.v
/tb
   tb_ip_name.v
   tb_fifo.v
   tb_alu.v
/sim
   run.do       // Questa/ModelSim script
   run.sh       // Icarus Verilog script
```

---

# **4. Example Run (Icarus Verilog)**

```bash
iverilog -o simv rtl/ip_name.v tb/tb_ip_name.v
vvp simv
gtkwave dump.vcd   # If waveform dumping enabled
```

---

👉 This skeleton can be extended to **any MNC/core company -style IP block** — FIFO, UART, AXI interface, cache, etc.


 the **standard top module format** that’s typically expected in RTL coding interviews (like at Qualcomm, NVIDIA, Intel, etc.).

Here’s the **clean skeleton/format** you can follow for **any Verilog IP RTL top module**:

---

### 🔹 **Top Module (RTL) Format**

```verilog
//============================================================
// Company    : Qualcomm (Example) 
// Engineer   : Your Name
// Design     : <IP Block Name>
// Description: Top-level RTL for <Functionality>
//============================================================

`timescale 1ns/1ps

module <ip_block_name> #(
    // ---------- Parameters ----------
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16
)(
    // ---------- Clock & Reset ----------
    input  wire                  clk,
    input  wire                  rst_n,  

    // ---------- Control Signals ----------
    input  wire                  enable,
    input  wire                  start,

    // ---------- Data Interfaces ----------
    input  wire [DATA_WIDTH-1:0] data_in,
    output reg  [DATA_WIDTH-1:0] data_out,

    // ---------- Status Signals ----------
    output reg                   done,
    output reg                   error
);

    // ---------- Internal Registers & Wires ----------
    reg  [DATA_WIDTH-1:0] reg_a;
    wire [DATA_WIDTH-1:0] result;

    // ---------- Submodule Instantiation (if any) ----------
    sub_module u_sub (
        .clk(clk),
        .rst_n(rst_n),
        .in_a(reg_a),
        .out_y(result)
    );

    // ---------- Sequential Logic ----------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_a   <= '0;
            data_out <= '0;
            done    <= 1'b0;
        end 
        else if (enable) begin
            if (start) begin
                reg_a   <= data_in;
                data_out <= result;
                done    <= 1'b1;
            end
        end
    end

endmodule
```

---

### 🔹 **Top Testbench (TB) Format**

```verilog
//============================================================
// Testbench for <IP Block Name>
//============================================================

`timescale 1ns/1ps

module tb_<ip_block_name>();

    // ---------- Parameters ----------
    parameter DATA_WIDTH = 32;
    parameter ADDR_WIDTH = 16;

    // ---------- DUT I/O ----------
    reg                   clk;
    reg                   rst_n;
    reg                   enable;
    reg                   start;
    reg  [DATA_WIDTH-1:0] data_in;
    wire [DATA_WIDTH-1:0] data_out;
    wire                  done;
    wire                  error;

    // ---------- DUT Instantiation ----------
    <ip_block_name> #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .start(start),
        .data_in(data_in),
        .data_out(data_out),
        .done(done),
        .error(error)
    );

    // ---------- Clock Generation ----------
    initial clk = 0;
    always #5 clk = ~clk;   // 100 MHz

    // ---------- Reset Task ----------
    task reset_dut;
    begin
        rst_n = 0;
        #20;
        rst_n = 1;
    end
    endtask

    // ---------- Stimulus ----------
    initial begin
        // Init
        enable   = 0;
        start    = 0;
        data_in  = 0;

        // Reset
        reset_dut();

        // Test Case 1
        #10 enable = 1;
        #10 start  = 1;
        data_in   = 32'hABCD_1234;
        #10 start  = 0;

        // Wait for done
        wait(done);
        $display("Test1 Done, Output = %h", data_out);

        // Add more test cases here
        #100 $finish;
    end

endmodule
```

---

👉 This **skeleton** is what Qualcomm/NVIDIA/Intel expect you to write cleanly:

* **Top module** with parameters, ports, internal logic.
* **Testbench** with DUT instantiation, clock/reset, stimulus, monitors.


