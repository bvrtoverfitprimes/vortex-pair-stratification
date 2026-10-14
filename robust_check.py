import json, os
import numpy as np
from diagnostics import Vcurve, w0_of

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
def load(n): return json.load(open(os.path.join(R, n + ".out.json")))
zq = np.array([0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6])
pairs = [("box s=0.3", ("L_neutral", "L_n1_s+0.30"), ("W_neutral", "W_n1_s+0.30")),
         ("box s=-0.2", ("L_neutral", "L_n1_s-0.20"), ("W_neutral", "W_n1_s-0.20")),
         ("grid s=0.3", ("L_neutral", "L_n1_s+0.30"), ("R_neutral", "R_n1_s+0.30")),
         ("grid s=-0.2", ("L_neutral", "L_n1_s-0.20"), ("R_neutral", "R_n1_s-0.20")),
         ("core s=0.3", ("L_neutral", "L_n1_s+0.30"), ("C_neutral", "C_n1_s+0.30")),
         ("core s=-0.2", ("L_neutral", "L_n1_s-0.20"), ("C_neutral", "C_n1_s-0.20"))]
for lab, (n1, r1), (n2, r2) in pairs:
    a = Vcurve(load(n1), load(r1), zq); b = Vcurve(load(n2), load(r2), zq)
    print(f"{lab:12s} w0 {w0_of(load(n2)):.3f}")
    print("   ref ", " ".join(f"{v:.3f}" for v in a))
    print("   alt ", " ".join(f"{v:.3f}" for v in b))
    print("   diff", " ".join(f"{v:+.3f}" for v in b - a), " rel", " ".join(f"{v:+.2f}" for v in (b - a) / a))
