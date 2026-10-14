import json, os
import numpy as np
from closure import TabKernel
from analyze_layers import profile_density
from diagnostics import speed_depth

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
def load(n): return json.load(open(os.path.join(R, n + ".out.json")))
d = np.load(os.path.join(R, "kernel_dns.npz")); tk = TabKernel(d["z"], d["s"], d["G"])
neu = load("L_neutral"); zn, wn = speed_depth(neu)
zq = np.array([0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6])
ss = np.linspace(d["s"][0] - 0.075, d["s"][-1] + 0.075, 6001)
for nm in ("B_u10", "B_u25", "B_u25_iB", "B_u25_iA", "B_u10_i2A"):
    r = load(nm); z, w = speed_depth(r)
    Vd = (np.interp(zq, zn, wn) ** 2 - np.interp(zq, z, w, right=np.nan) ** 2) / 2
    dens = profile_density(r["cfg"], ss)
    Vk = np.trapezoid(tk.G(zq[:, None], ss[None, :]) * dens[None, :], ss, axis=1)
    print(nm, "max depth", round(max(z), 3))
    print("  DNS   ", " ".join(f"{v:.3f}" for v in Vd))
    print("  kernel", " ".join(f"{v:.3f}" for v in Vk))
    print("  diff  ", " ".join(f"{a-b:+.3f}" for a, b in zip(Vd, Vk)))
