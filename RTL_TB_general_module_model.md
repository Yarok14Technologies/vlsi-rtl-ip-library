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

 **Qualcomm, NVIDIA, Intel, Broadcom**, etc., they often expect you to know the **standard top module format with AXI/APB interfaces**, since most IPs are part of a bigger SoC.

Here’s a **clean skeleton** for both **AXI4-Lite** (common for register access) and **APB**. You can use/adapt this in any interview or coding round:

---

## 🔹 **AXI4-Lite Top Module (Skeleton)**

```verilog
//============================================================
// Company    : Qualcomm (Example)
// Engineer   : Your Name
// Design     : AXI4-Lite Peripheral Example
//============================================================

`timescale 1ns/1ps

module axi_peripheral #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    // ---------- Clock & Reset ----------
    input  wire                   aclk,
    input  wire                   aresetn,

    // ---------- AXI Write Address Channel ----------
    input  wire [ADDR_WIDTH-1:0]  s_axi_awaddr,
    input  wire                   s_axi_awvalid,
    output reg                    s_axi_awready,

    // ---------- AXI Write Data Channel ----------
    input  wire [DATA_WIDTH-1:0]  s_axi_wdata,
    input  wire [(DATA_WIDTH/8)-1:0] s_axi_wstrb,
    input  wire                   s_axi_wvalid,
    output reg                    s_axi_wready,

    // ---------- AXI Write Response Channel ----------
    output reg  [1:0]             s_axi_bresp,
    output reg                    s_axi_bvalid,
    input  wire                   s_axi_bready,

    // ---------- AXI Read Address Channel ----------
    input  wire [ADDR_WIDTH-1:0]  s_axi_araddr,
    input  wire                   s_axi_arvalid,
    output reg                    s_axi_arready,

    // ---------- AXI Read Data Channel ----------
    output reg [DATA_WIDTH-1:0]   s_axi_rdata,
    output reg [1:0]              s_axi_rresp,
    output reg                    s_axi_rvalid,
    input  wire                   s_axi_rready
);

    // ---------- Internal Registers ----------
    reg [DATA_WIDTH-1:0] regfile [0:15]; // 16 registers

    // ---------- AXI Write Logic ----------
    always @(posedge aclk) begin
        if (!aresetn) begin
            s_axi_awready <= 0;
            s_axi_wready  <= 0;
            s_axi_bvalid  <= 0;
        end else begin
            if (s_axi_awvalid && !s_axi_awready) s_axi_awready <= 1;
            else s_axi_awready <= 0;

            if (s_axi_wvalid && !s_axi_wready) begin
                regfile[s_axi_awaddr[5:2]] <= s_axi_wdata;
                s_axi_wready <= 1;
                s_axi_bvalid <= 1;
                s_axi_bresp  <= 2'b00; // OKAY
            end else begin
                s_axi_wready <= 0;
                if (s_axi_bready) s_axi_bvalid <= 0;
            end
        end
    end

    // ---------- AXI Read Logic ----------
    always @(posedge aclk) begin
        if (!aresetn) begin
            s_axi_arready <= 0;
            s_axi_rvalid  <= 0;
        end else begin
            if (s_axi_arvalid && !s_axi_arready) begin
                s_axi_arready <= 1;
                s_axi_rdata   <= regfile[s_axi_araddr[5:2]];
                s_axi_rvalid  <= 1;
                s_axi_rresp   <= 2'b00; // OKAY
            end else begin
                s_axi_arready <= 0;
                if (s_axi_rready) s_axi_rvalid <= 0;
            end
        end
    end

endmodule
```

---

## 🔹 **APB Top Module (Skeleton)**

```verilog
//============================================================
// Design : APB Peripheral Example
//============================================================

`timescale 1ns/1ps

module apb_peripheral #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32
)(
    // ---------- Clock & Reset ----------
    input  wire                  pclk,
    input  wire                  presetn,

    // ---------- APB Bus ----------
    input  wire                  psel,
    input  wire                  penable,
    input  wire                  pwrite,
    input  wire [ADDR_WIDTH-1:0] paddr,
    input  wire [DATA_WIDTH-1:0] pwdata,
    output reg  [DATA_WIDTH-1:0] prdata,
    output reg                   pready
);

    // ---------- Internal Registers ----------
    reg [DATA_WIDTH-1:0] regfile [0:15]; // 16 registers

    // ---------- APB Logic ----------
    always @(posedge pclk) begin
        if (!presetn) begin
            pready <= 0;
            prdata <= 0;
        end else begin
            pready <= 0;
            if (psel && penable) begin
                pready <= 1;
                if (pwrite) begin
                    regfile[paddr[5:2]] <= pwdata;
                end else begin
                    prdata <= regfile[paddr[5:2]];
                end
            end
        end
    end

endmodule
```

---

👉 At Qualcomm/NVIDIA, you’ll usually be asked to:

* Write a **simple AXI4-Lite or APB slave** (register file).
* Show how you’d connect it to a **testbench** (driver → DUT → monitor).
* Extend it to support **interrupts, status bits, FIFOs, or handshake logic**.

---

🔥 Great — let’s do the **AXI4-Lite TB** and **APB TB**.
In Qualcomm-style interviews, they love when you show **driver tasks** (write/read), clean **clock/reset**, and **monitors** for responses.

---

# ✅ **AXI4-Lite Testbench Skeleton**

```verilog
//============================================================
// Testbench : AXI4-Lite Peripheral
//============================================================
`timescale 1ns/1ps

module tb_axi_peripheral;

    // ---------- Parameters ----------
    parameter ADDR_WIDTH = 32;
    parameter DATA_WIDTH = 32;

    // ---------- Signals ----------
    reg                    aclk;
    reg                    aresetn;

    reg  [ADDR_WIDTH-1:0]  s_axi_awaddr;
    reg                    s_axi_awvalid;
    wire                   s_axi_awready;

    reg  [DATA_WIDTH-1:0]  s_axi_wdata;
    reg  [(DATA_WIDTH/8)-1:0] s_axi_wstrb;
    reg                    s_axi_wvalid;
    wire                   s_axi_wready;

    wire [1:0]             s_axi_bresp;
    wire                   s_axi_bvalid;
    reg                    s_axi_bready;

    reg  [ADDR_WIDTH-1:0]  s_axi_araddr;
    reg                    s_axi_arvalid;
    wire                   s_axi_arready;

    wire [DATA_WIDTH-1:0]  s_axi_rdata;
    wire [1:0]             s_axi_rresp;
    wire                   s_axi_rvalid;
    reg                    s_axi_rready;

    // ---------- DUT ----------
    axi_peripheral dut (
        .aclk(aclk),
        .aresetn(aresetn),
        .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_wdata(s_axi_wdata),
        .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wvalid(s_axi_wvalid),
        .s_axi_wready(s_axi_wready),
        .s_axi_bresp(s_axi_bresp),
        .s_axi_bvalid(s_axi_bvalid),
        .s_axi_bready(s_axi_bready),
        .s_axi_araddr(s_axi_araddr),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_rdata(s_axi_rdata),
        .s_axi_rresp(s_axi_rresp),
        .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready)
    );

    // ---------- Clock ----------
    initial aclk = 0;
    always #5 aclk = ~aclk; // 100 MHz

    // ---------- Reset ----------
    initial begin
        aresetn = 0;
        #20 aresetn = 1;
    end

    // ---------- AXI Write Task ----------
    task axi_write(input [ADDR_WIDTH-1:0] addr, input [DATA_WIDTH-1:0] data);
    begin
        // Address phase
        s_axi_awaddr  = addr;
        s_axi_awvalid = 1;
        @(posedge aclk);
        while (!s_axi_awready) @(posedge aclk);
        s_axi_awvalid = 0;

        // Data phase
        s_axi_wdata   = data;
        s_axi_wstrb   = 'hF;
        s_axi_wvalid  = 1;
        @(posedge aclk);
        while (!s_axi_wready) @(posedge aclk);
        s_axi_wvalid  = 0;

        // Response
        s_axi_bready  = 1;
        @(posedge aclk);
        while (!s_axi_bvalid) @(posedge aclk);
        $display("AXI WRITE: Addr=0x%0h, Data=0x%0h, Resp=%0b", addr, data, s_axi_bresp);
        s_axi_bready  = 0;
    end
    endtask

    // ---------- AXI Read Task ----------
    task axi_read(input [ADDR_WIDTH-1:0] addr, output [DATA_WIDTH-1:0] data);
    begin
        // Address phase
        s_axi_araddr  = addr;
        s_axi_arvalid = 1;
        @(posedge aclk);
        while (!s_axi_arready) @(posedge aclk);
        s_axi_arvalid = 0;

        // Data phase
        s_axi_rready  = 1;
        @(posedge aclk);
        while (!s_axi_rvalid) @(posedge aclk);
        data = s_axi_rdata;
        $display("AXI READ: Addr=0x%0h, Data=0x%0h, Resp=%0b", addr, data, s_axi_rresp);
        s_axi_rready  = 0;
    end
    endtask

    // ---------- Stimulus ----------
    reg [31:0] rdata;
    initial begin
        // Init
        s_axi_awaddr = 0; s_axi_awvalid = 0;
        s_axi_wdata = 0;  s_axi_wstrb = 0; s_axi_wvalid = 0;
        s_axi_bready = 0;
        s_axi_araddr = 0; s_axi_arvalid = 0; s_axi_rready = 0;

        @(posedge aresetn);

        // Testcase 1: Write & Read
        axi_write(32'h04, 32'hDEAD_BEEF);
        axi_read(32'h04, rdata);

        #50 $finish;
    end

endmodule
```

---

# ✅ **APB Testbench Skeleton**

```verilog
//============================================================
// Testbench : APB Peripheral
//============================================================
`timescale 1ns/1ps

module tb_apb_peripheral;

    // ---------- Parameters ----------
    parameter ADDR_WIDTH = 8;
    parameter DATA_WIDTH = 32;

    // ---------- Signals ----------
    reg                   pclk;
    reg                   presetn;
    reg                   psel;
    reg                   penable;
    reg                   pwrite;
    reg  [ADDR_WIDTH-1:0] paddr;
    reg  [DATA_WIDTH-1:0] pwdata;
    wire [DATA_WIDTH-1:0] prdata;
    wire                  pready;

    // ---------- DUT ----------
    apb_peripheral dut (
        .pclk(pclk),
        .presetn(presetn),
        .psel(psel),
        .penable(penable),
        .pwrite(pwrite),
        .paddr(paddr),
        .pwdata(pwdata),
        .prdata(prdata),
        .pready(pready)
    );

    // ---------- Clock ----------
    initial pclk = 0;
    always #10 pclk = ~pclk; // 50 MHz

    // ---------- Reset ----------
    initial begin
        presetn = 0;
        #30 presetn = 1;
    end

    // ---------- APB Write Task ----------
    task apb_write(input [ADDR_WIDTH-1:0] addr, input [DATA_WIDTH-1:0] data);
    begin
        @(posedge pclk);
        psel   = 1; pwrite = 1; paddr = addr; pwdata = data; penable = 0;
        @(posedge pclk);
        penable = 1;
        wait(pready);
        @(posedge pclk);
        psel = 0; penable = 0;
        $display("APB WRITE: Addr=0x%0h, Data=0x%0h", addr, data);
    end
    endtask

    // ---------- APB Read Task ----------
    task apb_read(input [ADDR_WIDTH-1:0] addr, output [DATA_WIDTH-1:0] data);
    begin
        @(posedge pclk);
        psel   = 1; pwrite = 0; paddr = addr; penable = 0;
        @(posedge pclk);
        penable = 1;
        wait(pready);
        @(posedge pclk);
        data = prdata;
        psel = 0; penable = 0;
        $display("APB READ: Addr=0x%0h, Data=0x%0h", addr, data);
    end
    endtask

    // ---------- Stimulus ----------
    reg [31:0] rdata;
    initial begin
        // Init
        psel=0; penable=0; pwrite=0; paddr=0; pwdata=0;

        @(posedge presetn);

        // Testcase 1: Write & Read
        apb_write(8'h04, 32'hCAFE_F00D);
        apb_read(8'h04, rdata);

        #100 $finish;
    end

endmodule
```

---

### ⚡ What these TBs demonstrate

* **Reusable driver tasks** → `axi_write/axi_read` and `apb_write/apb_read`.
* **Handshake correctness** → Waits for `ready/valid` (AXI) and `pready` (APB).
* **Stimulus flow** → Reset → Write → Read → Check result.

---

👉 **cleanly in an interview**, you score **big points**.
👉 extend TB to have **random transactions, scoreboard, and coverage (UVM style)**.

---

