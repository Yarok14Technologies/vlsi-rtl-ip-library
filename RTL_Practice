# **Part 1: FSMs (Problems 1–8)**

### **1. Sequence Detector 1011 (Mealy Overlapping)**

```verilog
module seq_detect_1011_mealy(
    input clk,
    input rst_n,
    input din,
    output reg detected
);
    reg [2:0] state, next_state;
    localparam S0=3'b000, S1=3'b001, S2=3'b010, S3=3'b011, S4=3'b100;

    always @(*) begin
        next_state = state;
        detected = 0;
        case(state)
            S0: next_state = din ? S1 : S0;
            S1: next_state = din ? S1 : S2;
            S2: next_state = din ? S3 : S0;
            S3: next_state = din ? S4 : S2;
            S4: begin
                detected = din; 
                next_state = din ? S1 : S2; 
            end
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= S0;
        else state <= next_state;
    end
endmodule
```

---

### **2. Sequence Detector 1011 (Mealy Non-Overlapping)**

```verilog
module seq_detect_1011_mealy_non(
    input clk,
    input rst_n,
    input din,
    output reg detected
);
    reg [2:0] state, next_state;
    localparam S0=3'b000, S1=3'b001, S2=3'b010, S3=3'b011;

    always @(*) begin
        next_state = state;
        detected = 0;
        case(state)
            S0: next_state = din ? S1 : S0;
            S1: next_state = din ? S1 : S2;
            S2: next_state = din ? S3 : S0;
            S3: begin
                detected = din;
                next_state = S0;  // non-overlapping
            end
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= S0;
        else state <= next_state;
    end
endmodule
```

---

### **3. Sequence Detector 1011 (Moore Overlapping)**

```verilog
module seq_detect_1011_moore(
    input clk,
    input rst_n,
    input din,
    output reg detected
);
    reg [2:0] state, next_state;
    localparam S0=3'b000, S1=3'b001, S2=3'b010, S3=3'b011, S4=3'b100;

    always @(*) begin
        next_state = state;
        case(state)
            S0: next_state = din ? S1 : S0;
            S1: next_state = din ? S1 : S2;
            S2: next_state = din ? S3 : S0;
            S3: next_state = din ? S4 : S2;
            S4: next_state = din ? S1 : S2;
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= S0;
        else state <= next_state;
    end

    always @(*) begin
        detected = (state == S4);
    end
endmodule
```

---

### **4. Sequence Detector 1011 (Moore Non-Overlapping)**

```verilog
module seq_detect_1011_moore_non(
    input clk,
    input rst_n,
    input din,
    output reg detected
);
    reg [2:0] state, next_state;
    localparam S0=3'b000, S1=3'b001, S2=3'b010, S3=3'b011;

    always @(*) begin
        next_state = state;
        case(state)
            S0: next_state = din ? S1 : S0;
            S1: next_state = din ? S1 : S2;
            S2: next_state = din ? S3 : S0;
            S3: next_state = S0; // non-overlapping
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= S0;
        else state <= next_state;
    end

    always @(*) begin
        detected = (state == S3);
    end
endmodule
```

---

### **5. Traffic Light Controller (4 States)**

```verilog
module traffic_light(
    input clk,
    input rst_n,
    output reg [2:0] lights // [Red, Yellow, Green]
);
    reg [1:0] state, next_state;
    localparam RED=2'b00, GREEN=2'b01, YELLOW=2'b10;

    always @(*) begin
        next_state = state;
        case(state)
            RED: next_state = GREEN;
            GREEN: next_state = YELLOW;
            YELLOW: next_state = RED;
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= RED;
        else state <= next_state;
    end

    always @(*) begin
        case(state)
            RED: lights = 3'b100;
            GREEN: lights = 3'b001;
            YELLOW: lights = 3'b010;
            default: lights = 3'b000;
        endcase
    end
endmodule
```

---

### **6. Round-Robin Arbiter (4 Requests)**

```verilog
module rr_arbiter_4(
    input clk,
    input rst_n,
    input [3:0] req,
    output reg [3:0] grant
);
    reg [1:0] last;

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            grant <= 4'b0000;
            last <= 2'b00;
        end else begin
            case(last)
                2'b00: grant <= req[0] ? 4'b0001 : (req[1] ? 4'b0010 : (req[2] ? 4'b0100 : (req[3] ? 4'b1000 : 4'b0000)));
                2'b01: grant <= req[1] ? 4'b0010 : (req[2] ? 4'b0100 : (req[3] ? 4'b1000 : (req[0] ? 4'b0001 : 4'b0000)));
                2'b10: grant <= req[2] ? 4'b0100 : (req[3] ? 4'b1000 : (req[0] ? 4'b0001 : (req[1] ? 4'b0010 : 4'b0000)));
                2'b11: grant <= req[3] ? 4'b1000 : (req[0] ? 4'b0001 : (req[1] ? 4'b0010 : (req[2] ? 4'b0100 : 4'b0000)));
            endcase

            if(grant != 0)
                last <= grant[3] ? 2'b11 : grant[2] ? 2'b10 : grant[1] ? 2'b01 : 2'b00;
        end
    end
endmodule
```

---

### **7. Multiply/Divide FSM Controller (Simplified)**

```verilog
module muldiv_fsm(
    input clk,
    input rst_n,
    input start_mul,
    input start_div,
    output reg busy,
    output reg done
);
    reg [1:0] state, next_state;
    localparam IDLE=2'b00, MUL=2'b01, DIV=2'b10, DONE=2'b11;

    always @(*) begin
        next_state = state;
        case(state)
            IDLE: if(start_mul) next_state = MUL; else if(start_div) next_state = DIV;
            MUL: next_state = DONE;
            DIV: next_state = DONE;
            DONE: next_state = IDLE;
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= IDLE;
        else state <= next_state;
    end

    always @(*) begin
        busy = (state==MUL)||(state==DIV);
        done = (state==DONE);
    end
endmodule
```

---

### **8. Elevator FSM (Up/Down Buttons)**

```verilog
module elevator_fsm(
    input clk,
    input rst_n,
    input up_btn,
    input down_btn,
    output reg [1:0] floor // 2-bit floor number 0-3
);
    reg [1:0] state, next_state;

    always @(*) begin
        next_state = state;
        if(up_btn) next_state = (state < 2'b11) ? state+1 : state;
        else if(down_btn) next_state = (state > 0) ? state-1 : state;
    end

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) state <= 0;
        else state <= next_state;
    end

    always @(*) floor = state;
endmodule
```


---

# ** Part 2: Counters, Shift Registers & Arithmetic Units**

---

## **9. Parameterized N-bit Synchronous Counter with Enable and Reset**

```verilog
module sync_counter #(parameter N=8)(
    input clk,
    input rst_n,
    input en,
    output reg [N-1:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
            count <= 0;
        else if(en)
            count <= count + 1;
    end
endmodule
```

✅ Parameterized width; synchronous counting with enable.

---

## **10. Up/Down Counter with Synchronous Reset**

```verilog
module up_down_counter #(parameter N=8)(
    input clk,
    input rst_n,
    input up,
    input down,
    output reg [N-1:0] count
);
    always @(posedge clk) begin
        if(!rst_n)
            count <= 0;
        else if(up)
            count <= count + 1;
        else if(down)
            count <= count - 1;
    end
endmodule
```

---

## **11. 4-bit Johnson Counter / Ring Counter**

```verilog
module johnson_counter #(parameter N=4)(
    input clk,
    input rst_n,
    output reg [N-1:0] q
);
    always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
            q <= 0;
        else
            q <= {~q[N-1], q[N-1:1]}; // Johnson sequence
    end
endmodule
```

✅ Johnson counter generates **2N unique states**.

---

## **12. Shift Register (Serial In/Out)**

```verilog
module shift_reg_serial #(parameter N=8)(
    input clk,
    input rst_n,
    input serial_in,
    output reg serial_out
);
    reg [N-1:0] shift;
    always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
            shift <= 0;
        else begin
            shift <= {shift[N-2:0], serial_in};
            serial_out <= shift[N-1];
        end
    end
endmodule
```

---

## **13. Shift Register with Parallel Load and Serial Output**

```verilog
module shift_reg_parallel #(parameter N=8)(
    input clk,
    input rst_n,
    input load,
    input [N-1:0] pdata,
    output reg q
);
    reg [N-1:0] shift;
    always @(posedge clk or negedge rst_n) begin
        if(!rst_n)
            shift <= 0;
        else if(load)
            shift <= pdata;
        else begin
            q <= shift[N-1];
            shift <= {shift[N-2:0], 1'b0};
        end
    end
endmodule
```

✅ Supports parallel load and serial shift.

---

## **14. Variable-Length Barrel Shifter (Left/Right)**

```verilog
module barrel_shifter #(parameter N=8)(
    input [N-1:0] data_in,
    input [2:0] shift_amt,
    input dir, // 0=left, 1=right
    output [N-1:0] data_out
);
    assign data_out = dir ? (data_in >> shift_amt) : (data_in << shift_amt);
endmodule
```

✅ Simple, parameterized, synthesizable.

---

## **15. 8x8 Unsigned Multiplier (Array Style)**

```verilog
module mult8x8(
    input [7:0] a,
    input [7:0] b,
    output [15:0] product
);
    assign product = a * b; // synthesizable
endmodule
```

✅ For interview, can also implement **manual array multiplier using generate loops**.

---

## **16. 16x16 Signed Multiplier (Booth Algorithm Simplified)**

```verilog
module mult16x16_signed(
    input signed [15:0] a,
    input signed [15:0] b,
    output signed [31:0] product
);
    assign product = a * b;
endmodule
```

✅ Booth can be implemented manually for deeper RTL understanding.

---

## **17. Parameterized Adder-Subtractor with Carry**

```verilog
module adder_sub #(parameter N=8)(
    input [N-1:0] a, b,
    input sub, // 0=add, 1=subtract
    output [N-1:0] sum,
    output carry
);
    assign {carry, sum} = sub ? (a - b) : (a + b);
endmodule
```

---

## **18. 8-bit ALU (AND, OR, ADD, SUB, XOR, SLT)**

```verilog
module alu8(
    input [7:0] a, b,
    input [2:0] sel,
    output reg [7:0] y
);
    always @(*) begin
        case(sel)
            3'b000: y = a & b;
            3'b001: y = a | b;
            3'b010: y = a + b;
            3'b011: y = a - b;
            3'b100: y = a ^ b;
            3'b101: y = (a < b) ? 8'b1 : 8'b0; // SLT
            default: y = 0;
        endcase
    end
endmodule
```

---

## **19. 8-bit Kogge-Stone Adder (Template)**

```verilog
module kogge_stone_adder8(
    input [7:0] a, b,
    output [7:0] sum,
    output carry
);
    wire [7:0] g, p;
    wire [7:0] c;

    assign g = a & b;
    assign p = a ^ b;
    assign c[0] = 0;

    // Propagate carries (Kogge-Stone simplified)
    assign c[1] = g[0] | (p[0] & c[0]);
    assign c[2] = g[1] | (p[1] & g[0]) | (p[1] & p[0] & c[0]);
    assign c[3] = g[2] | (p[2]&g[1]) | (p[2]&p[1]&g[0]) | (p[2]&p[1]&p[0]&c[0]);
    assign c[4] = g[3] | (p[3]&g[2]) | (p[3]&p[2]&g[1]) | (p[3]&p[2]&p[1]&g[0]) | (p[3]&p[2]&p[1]&p[0]&c[0]);
    assign c[5] = g[4] | (p[4]&g[3]) | (p[4]&p[3]&g[2]) | (p[4]&p[3]&p[2]&g[1]) | (p[4]&p[3]&p[2]&p[1]&g[0]) | (p[4]&p[3]&p[2]&p[1]&p[0]&c[0]);
    assign c[6] = g[5] | (p[5]&g[4]) | (p[5]&p[4]&g[3]) | (p[5]&p[4]&p[3]&g[2]) | (p[5]&p[4]&p[3]&p[2]&g[1]) | (p[5]&p[4]&p[3]&p[2]&p[1]&g[0]) | (p[5]&p[4]&p[3]&p[2]&p[1]&p[0]&c[0]);
    assign c[7] = g[6] | (p[6]&g[5]) | (p[6]&p[5]&g[4]) | (p[6]&p[5]&p[4]&g[3]) | (p[6]&p[5]&p[4]&p[3]&g[2]) | (p[6]&p[5]&p[4]&p[3]&p[2]&g[1]) | (p[6]&p[5]&p[4]&p[3]&p[2]&p[1]&g[0]) | (p[6]&p[5]&p[4]&p[3]&p[2]&p[1]&p[0]&c[0]);
    assign carry = g[7] | (p[7]&g[6]) | (p[7]&p[6]&g[5]) | (p[7]&p[6]&p[5]&g[4]) | (p[7]&p[6]&p[5]&p[4]&g[3]) | (p[7]&p[6]&p[5]&p[4]&p[3]&g[2]) | (p[7]&p[6]&p[5]&p[4]&p[3]&p[2]&g[1]) | (p[7]&p[6]&p[5]&p[4]&p[3]&p[2]&p[1]&g[0]) | (p[7]&p[6]&p[5]&p[4]&p[3]&p[2]&p[1]&p[0]&c[0]);
    assign sum = p ^ c;
endmodule
```

✅ Can be extended for 16/32-bit versions; demonstrates **carry-lookahead design**.

---

## **20. 8-bit Carry-Save Multiplier Template**

```verilog
module carry_save_mult8(
    input [7:0] a, b,
    output [15:0] product
);
    wire [7:0] pp [7:0]; // partial products

    genvar i;
    generate
        for(i=0;i<8;i=i+1)
            assign pp[i] = b[i] ? a : 8'b0;
    endgenerate

    // Add partial products manually using CSA tree (simplified here)
    assign product = (pp[0]<<0) + (pp[1]<<1) + (pp[2]<<2) + (pp[3]<<3) + (pp[4]<<4) + (pp[5]<<5) + (pp[6]<<6) + (pp[7]<<7);
endmodule
```

---

## **21. Floating-Point Adder (IEEE-754 Simplified)**

```verilog
module fp_add(
    input [31:0] a, b,
    output [31:0] sum
);
    assign sum = $bitstoreal($realtobits($bitstoreal(a) + $bitstoreal(b))); 
    // Simplified for RTL interview; can implement full IEEE normalization
endmodule
```


