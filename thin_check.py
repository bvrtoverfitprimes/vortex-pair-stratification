import json, os
import numpy as np
from diagnostics import Vcurve

R = "runs"
def load(n): return json.load(open(os.path.join(R, n + ".out.json")))
neu = load("R_neutral")
zq = np.array([0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6])
WE = ((0.15, 0.03), (0.075, 0.015), (0.0375, 0.015))
var = np.array([w * w / 12 + np.pi ** 2 * e * e / 12 for w, e in WE])
print("rms thickness", np.round(np.sqrt(var), 4))
mx_thin, mx_base, mx_ext = 0.0, 0.0, 0.0
for c in (-0.625, -0.325, 0.075, 0.775):
    G = []
    for w, e in WE:
        n = f"T_c{c:+.3f}_w{w:.4f}"
        if not os.path.exists(os.path.join(R, n + ".out.json")):
            break
        G.append(Vcurve(neu, load(n), zq) / 0.5)
    if len(G) < 3:
        print(c, "incomplete"); continue
    G = np.array(G)
    G0 = G[2] - (G[1] - G[2]) * var[2] / (var[1] - var[2])
    print(f"c={c:+.3f}")
    for (w, e), g in zip(WE, G):
        print(f"   w={w:.4f} " + " ".join(f"{v:.3f}" for v in g))
    print(f"   extrap   " + " ".join(f"{v:.3f}" for v in G0))
    mx_thin = max(mx_thin, np.nanmax(abs(G[1] - G[2])))
    mx_base = max(mx_base, np.nanmax(abs(G[0] - G[2])))
    mx_ext = max(mx_ext, np.nanmax(abs(G[0] - G0)))
print(f"max |G(0.075)-G(0.0375)| = {mx_thin:.4f}; max |G(0.15)-G(0.0375)| = {mx_base:.4f}; "
      f"max |G(0.15)-G0| = {mx_ext:.4f}")
