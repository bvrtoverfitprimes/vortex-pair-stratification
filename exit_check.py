import json, os
import numpy as np
from closure import TabKernel, exit_time
from analyze_layers import profile_density, first_time
from diagnostics import speed_depth, w0_of

R = "runs"
def load(n): return json.load(open(os.path.join(R, n + ".out.json")))
d = np.load(os.path.join(R, "kernel_dns.npz")); tk = TabKernel(d["z"], d["s"], d["G"])
ss = np.linspace(d["s"][0] - 0.075, d["s"][-1] + 0.075, 6001)
neu = load("L_neutral"); w0 = w0_of(neu); zn, wn = speed_depth(neu)
tn, zcn = np.array(neu["t"]), np.array(neu["zc"])
runs = ["B_u10", "B_u25", "B_u25_iB", "B_u25_iA", "B_u10_i2A"] + \
       [f"L_n1_s{s:+.2f}" for s in (-0.4, -0.2, 0.0, 0.15, 0.3, 0.5, 0.75, 1.0)]
worst = [0, 0]
for nm in runs:
    r = load(nm); out = []
    for D in (0.5, 1.0, 1.4):
        zg = np.linspace(0, D, 401)
        V = np.trapezoid(tk.G(zg[:, None], ss[None, :]) * profile_density(r["cfg"], ss)[None, :], ss, axis=1)
        dns = first_time(r["t"], r["zc"], D) - first_time(tn, zcn, D)
        wnz = np.interp(zg, zn, wn); wnz[0] = wnz[1]
        g = wnz ** 2 - 2 * V
        full = np.inf if np.any(g <= 0) else np.trapezoid(1 / np.sqrt(g), zg) - np.trapezoid(1 / wnz, zg)
        norm = (exit_time(V / w0 ** 2, zg, 1.0) - D) / w0
        out.append(f"D={D}: dns {dns:.3f} full {full:.3f} norm {norm:.3f}")
        if np.isfinite(dns) and np.isfinite(norm):
            worst[0] = max(worst[0], abs(norm - full)); worst[1] = max(worst[1], abs(norm - dns))
    print(f"{nm:12s} " + " | ".join(out))
print(f"max |norm - full| = {worst[0]:.4f}, max |norm - dns| = {worst[1]:.4f}, w0 = {w0:.4f}")
