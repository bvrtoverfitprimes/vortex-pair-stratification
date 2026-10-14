import json, os
import numpy as np
from closure import Kernel, KAPPA_OVAL
from analyze_layers import model_traj, first_time, p2p_traj

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
def load(n): return json.load(open(os.path.join(R, n + ".out.json")))
neu = load("L_neutral"); tn, zn = np.array(neu["t"]), np.array(neu["zc"])
m = (tn > 0.5) & (tn < 3); w0 = np.polyfit(tn[m], zn[m], 1)[0]
ov, lo = Kernel(), Kernel(local=True)
for n in (1, 2):
    for s in (-0.4, -0.2, 0.0, 0.15, 0.3, 0.5, 0.75, 1.0, 1.5):
        name = f"L_n{n}_s{s:+.2f}"
        if not os.path.exists(os.path.join(R, name + ".out.json")):
            continue
        r = load(name); cfg = r["cfg"]
        out = []
        for D in (1.0, 1.5, 2.0):
            ts = first_time(r["t"], r["zc"], D) - first_time(tn, zn, D)
            zg, tl = model_traj(lo, KAPPA_OVAL, cfg, w0, 4.0); pl = np.interp(D, zg, tl) - D / w0
            zg, tq = p2p_traj(cfg, w0); pq = np.interp(D, zg, tq) - D / w0
            zg, to = model_traj(ov, KAPPA_OVAL, cfg, w0, 4.0); po = np.interp(D, zg, to) - D / w0
            out.append(f"D={D}: dns {ts:.3f} loc {pl:.3f} p2p {pq:.3f} ov {po:.3f}")
        print(f"n={n} s={s:+.2f} | " + " | ".join(out), flush=True)
