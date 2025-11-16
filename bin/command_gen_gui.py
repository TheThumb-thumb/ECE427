import tkinter as tk
from tkinter import ttk, messagebox

# -------------------- Memory Map --------------------
memory_map = [
    {"category": "Mux Select", "access": "R", "function": "Default state", "address": 0x00, "desc": "Mux selects controlled from here by default", "bits": 21},
    {"category": "Mux Select", "access": "R", "function": "Debug state", "address": 0x01, "desc": "Mux select controlled from here when debug is high", "bits": 21},
    {"category": "Control", "access": "R/W", "function": "Output Buffer Control", "address": 0x02, "desc": "Output buffer clock divider control and Trivium disable", "bits": 6},
    {"category": "Entropy Source Status", "access": "R", "function": "Entropy Status Latch [0:15]", "address": 0x03, "desc": "Entropy Status Latch [0:15]", "bits": 16},
    {"category": "Entropy Source Status", "access": "R", "function": "Entropy Status Latch [16:31]", "address": 0x04, "desc": "Entropy Status Latch [16:31]", "bits": 16},
    {"category": "Entropy Source Status", "access": "R", "function": "Entropy Status Jitter [0:15]", "address": 0x05, "desc": "Entropy Status Jitter [0:15]", "bits": 16},
    {"category": "Entropy Source Status", "access": "R", "function": "Entropy Status Jitter [16:31]", "address": 0x06, "desc": "Entropy Status Latch [16:31]", "bits": 16},
    {"category": "Entropy Control", "access": "R/W", "function": "Calibration bits for Latch", "address": 0x07, "desc": "Calibration bits for latch debug", "bits": 16},
    {"category": "Trimming", "access": "R/W", "function": "Temp sensor threshold 0", "address": 0x08, "desc": "Temp sensor 0 threshold", "bits": 14},
    {"category": "Trimming", "access": "R/W", "function": "Temp sensor threshold 1", "address": 0x09, "desc": "Temp sensor 1 threshold", "bits": 14},
    {"category": "Trimming", "access": "R/W", "function": "Temp sensor threshold 2", "address": 0x0A, "desc": "Temp sensor 2 threshold", "bits": 14},
    {"category": "Trimming", "access": "R/W", "function": "Temp sensor threshold 3", "address": 0x0B, "desc": "Temp sensor 3 threshold", "bits": 14},
    {"category": "Internal State", "access": "R", "function": "Temp Sensor 0 counter", "address": 0x0C, "desc": "Temp Sensor 0 counter", "bits": 14},
    {"category": "Internal State", "access": "R", "function": "Temp Sensor 1 counter", "address": 0x0D, "desc": "Temp Sensor 1 counter", "bits": 14},
    {"category": "Internal State", "access": "R", "function": "Temp Sensor 2 counter", "address": 0x0E, "desc": "Temp Sensor 2 counter", "bits": 14},
    {"category": "Internal State", "access": "R", "function": "Temp Sensor 3 counter", "address": 0x0F, "desc": "Temp Sensor 3 counter", "bits": 14},
]

# -------------------- Bit-packing --------------------
def pack_register_op(vals):
    """Pack 22-bit command for register operation"""
    cmd = 0
    cmd |= (1 << 21)  # curr_state[21] = 1 (register op)
    cmd |= ((vals["rw"]) & 0x1) << 20  # curr_state[20]
    cmd |= ((vals["addr"]) & 0xF) << 16  # curr_state[19:16]
    cmd |= (vals["data"] & 0xFFFF)  # curr_state[15:0]
    return cmd

# -------------------- Mux v4 Config --------------------
modules_out = {0: "VCC/CLK/Temp Sensor", 1: "Latch RNG 0–31 to output pin", 2: "Jitter RNG 0–31 to output pin"}
modules_in = {0: "No external input", 1: "OHT Latch 0–31 input from pin", 2: "OHT Jitter 0–31 input from pin", 3: "Conditioner/Trivium/AES input"}
mux0_cell_opts = {0: "VCC", 1: "CLK", 2: "Temp sensor 0", 3: "Temp sensor 1", 4: "Temp sensor 2", 5: "Temp sensor 3"}
mux3_cell_opts = {0: "Conditioner input", 1: "Trivium input", 2: "AES CTR input"}

def pack_curr_state(v):
    curr_state = 0
    curr_state |= (v["in_cell"] & 0x1F) << 0  # [4:0]
    curr_state |= (v["in_mod"] & 0x3) << 5    # [6:5]
    curr_state |= (v["out1_cell"] & 0x1F) << 7   # [11:7]
    curr_state |= (v["out1_mod"] & 0x3) << 12    # [13:12]
    curr_state |= (v["out2_cell"] & 0x1F) << 14  # [18:14]
    curr_state |= (v["out2_mod"] & 0x3) << 19    # [20:19]
    curr_state |= (v["op"] & 0x1) << 21          # [21]
    return curr_state

def make_cell_select(parent, label_text):
    frame = ttk.Frame(parent)
    ttk.Label(frame, text=label_text).pack(anchor="w")
    value = tk.IntVar(value=0)
    entry = ttk.Entry(frame, width=8)
    entry.insert(0, "0")
    entry.pack(anchor="w")
    return frame, value, entry


def update_cell_widget(frame, entry, var, module_val, mux_type, is_input=False):
    for w in frame.winfo_children():
        w.destroy()
    ttk.Label(frame, text=f"{mux_type} Cell Select").pack(anchor="w")
    
    if not is_input:
        if module_val == 0:
            cb = ttk.Combobox(frame, values=[f"{k}: {v}" for k,v in mux0_cell_opts.items()],
                              state="readonly", width=40)
            cb.current(0)
            cb.bind("<<ComboboxSelected>>", lambda e: var.set(int(cb.get().split(':')[0])))
            cb.pack(anchor="w")
            var.set(0)
        elif module_val in [1,2]:
            frm = ttk.Frame(frame); frm.pack(anchor="w")
            ttk.Label(frm, text="Index (0–31):").pack(side="left")
            entry = ttk.Entry(frm, width=5); entry.insert(0,"0"); entry.pack(side="left")
            entry.bind("<KeyRelease>", lambda e: var.set(int(entry.get() or 0)))
            var.set(0)
    else:
        if module_val == 0:
            ttk.Label(frame, text="(No input selected)").pack(anchor="w")
            var.set(0)
        elif module_val in [1,2]:
            frm = ttk.Frame(frame); frm.pack(anchor="w")
            ttk.Label(frm, text="Index (0–31):").pack(side="left")
            entry = ttk.Entry(frm, width=5); entry.insert(0,"0"); entry.pack(side="left")
            entry.bind("<KeyRelease>", lambda e: var.set(int(entry.get() or 0)))
            var.set(0)
        elif module_val == 3:
            cb = ttk.Combobox(frame, values=[f"{k}: {v}" for k,v in mux3_cell_opts.items()],
                              state="readonly", width=40)
            cb.current(0)
            cb.bind("<<ComboboxSelected>>", lambda e: var.set(int(cb.get().split(':')[0])))
            cb.pack(anchor="w")
            var.set(0)

def make_mux_section(parent, label, module_dict, mux_type, is_input=False):
    ttk.Label(parent, text=label, font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(6,2))
    mod_var = tk.IntVar(value=0)
    mod_cb = ttk.Combobox(parent, values=[f"{k} - {v}" for k,v in module_dict.items()],
                          state="readonly", width=45)
    mod_cb.current(0)
    mod_cb.pack(anchor="w")
    frame, cell_var, entry = make_cell_select(parent, f"{mux_type} Cell Select")
    frame.pack(anchor="w", pady=(0,4))
    def on_mod_change(e):
        mod_val = int(mod_cb.get().split('-')[0].strip())
        mod_var.set(mod_val)
        update_cell_widget(frame, entry, cell_var, mod_val, mux_type, is_input=is_input)
    mod_cb.bind("<<ComboboxSelected>>", on_mod_change)
    return mod_var, cell_var

# -------------------- GUI --------------------
root = tk.Tk()
root.title("Debug Command Generator")
root.geometry("700x800")

op_var = tk.IntVar(value=0)
rw_var = tk.IntVar(value=0)
addr_var = tk.IntVar(value=0)
data_var = tk.StringVar(value="0000")
output_var = tk.StringVar()

ttk.Label(root, text="Select Operation Mode").pack(anchor="w", pady=(10,0))
ttk.Radiobutton(root, text="0 - Mux configuration (write to debug state register)", variable=op_var, value=0).pack(anchor="w")
ttk.Radiobutton(root, text="1 - Register operation (read/write)", variable=op_var, value=1).pack(anchor="w")

mux_frame = ttk.Frame(root)
reg_frame = ttk.Frame(root)

# -------------------- Mux Config Section --------------------
out2_mod_var, out2_cell_var = make_mux_section(mux_frame, "Output Pin Mux 2", modules_out, "Output Mux 2")
out1_mod_var, out1_cell_var = make_mux_section(mux_frame, "Output Pin Mux 1", modules_out, "Output Mux 1")
in_mod_var, in_cell_var = make_mux_section(mux_frame, "Input Pin Mux", modules_in, "Input Mux", is_input=True)

# -------------------- Register Operation Section --------------------
ttk.Label(reg_frame, text="Register Operation", font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(8,4))
rw_cb = ttk.Combobox(reg_frame, values=["0 - Write", "1 - Read"], state="readonly", width=20)
rw_cb.current(0)
rw_cb.pack(anchor="w", pady=2)
rw_cb.bind("<<ComboboxSelected>>", lambda e: rw_var.set(int(rw_cb.get().split('-')[0].strip())))

addr_cb = ttk.Combobox(reg_frame, values=[], state="readonly", width=60)
addr_cb.pack(anchor="w", pady=4)

def update_addr_values(*args):
    # Filter addresses based on RW selection
    rw = rw_var.get()
    if rw == 0:  # Write
        filtered = [m for m in memory_map if "W" in m["access"]]
    else:  # Read
        filtered = memory_map  # All can be read

    addr_values = [f"0x{m['address']:02X} - {m['category']} - {m['function']} - {m['bits']} bits" for m in filtered]
    addr_cb['values'] = addr_values

    if filtered:
        addr_cb.current(0)
        addr_var.set(filtered[0]['address'])  # already an integer

    # Rebind selection to properly parse hex
    def on_addr_change(e):
        addr_str = addr_cb.get().split('-')[0].strip()
        addr_var.set(int(addr_str, 16))  # <- parse as hex

    addr_cb.bind("<<ComboboxSelected>>", on_addr_change)

rw_var.trace("w", update_addr_values)
update_addr_values()



# Data entry
data_frame = ttk.Frame(reg_frame)
ttk.Label(data_frame, text="Write Data (hex, up to 16 bits):").pack(side="left")
data_entry = ttk.Entry(data_frame, textvariable=data_var, width=10)
data_entry.pack(side="left")
data_frame.pack(anchor="w", pady=4)


def toggle_data_entry(*_):
    if rw_var.get() == 0:  # Write
        data_entry.config(state="normal")
    else:  # Read
        data_entry.config(state="disabled")

rw_var.trace("w", toggle_data_entry)
toggle_data_entry()  # Set initial state

def toggle_views(*_):
    if op_var.get() == 0:
        mux_frame.pack(anchor="w", fill="x", padx=10, pady=5)
        reg_frame.forget()
    else:
        reg_frame.pack(anchor="w", fill="x", padx=10, pady=5)
        mux_frame.forget()
op_var.trace("w", toggle_views)
toggle_views()



def generate():
    if op_var.get() == 0:
        vals = {
            "in_cell": in_cell_var.get(),
            "in_mod": in_mod_var.get(),
            "out1_cell": out1_cell_var.get(),
            "out1_mod": out1_mod_var.get(),
            "out2_cell": out2_cell_var.get(),
            "out2_mod": out2_mod_var.get(),
            "op": 0
        }
        cmd = pack_curr_state(vals)
        output_var.set(f"0x{cmd:06X}")
        # Print breakdown
        print(f"Command: 0x{cmd:06X} / {cmd:022b} (binary)")
        print("Breakdown:")
        for k, v in vals.items():
            print(f"  {k}: {v}")

    else:
        try:
            data = int(data_var.get(), 16) if rw_var.get() == 0 else 0
        except ValueError:
            messagebox.showerror("Invalid Data", "Enter valid hexadecimal data.")
            return
        vals = {"rw": rw_var.get(), "addr": addr_var.get(), "data": data}
        cmd = pack_register_op(vals)
        output_var.set(f"0x{cmd:06X}")
        # Print breakdown
        print(f"Command: 0x{cmd:06X} / {cmd:022b} (binary)")
        print("Breakdown:")
        for k, v in vals.items():
            print(f"  {k}: {v}")

    print("-" * 40)


ttk.Button(root, text="Generate 22-bit Command", command=generate).pack(anchor="w", pady=8)
ttk.Label(root, text="Generated Command:").pack(anchor="w")
ttk.Label(root, textvariable=output_var, font=("Consolas", 12), foreground="blue").pack(anchor="w", pady=(0,10))

root.mainloop()
