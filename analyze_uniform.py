import json, sys
import numpy as np
from scipy.optimize import least_squares

R = "runs/"
def load(n): return json.load(open(R + n + ".out.json"))

for L in (8, 16):
    neu = load(f"n_L{L}")
    t = np.array(neu["t"]); zn = np.array(neu["zc"])
    w0 = np.polyfit(t[(t > 0.5) & (t < 3)], zn[(t > 0.5) & (t < 3)], 1)[0]
    print(f"Lx={L}: neutral w0 = {w0:.4f}")
    for N2 in (0.25, 0.5, 1.0):
        try:
            r = load(f"u_{N2}_L{L}")
        except FileNotFoundError:
            continue
        t = np.array(r["t"]); z = np.array(r["zc"])
        dz = np.interp(t, np.array(neu["t"]), zn) - z
        N = np.sqrt(N2)
        out = []
        for kap in (0.4536, 1.0):
            om = np.sqrt(kap) * N
            zm = w0 * np.sin(om * t) / om
            dm = w0 * t - zm
            out.append(dm)
        m = t <= min(4.0, t[np.argmax(z)] + 1e-9) if z.max() < z[-1] + 1e-9 else t <= t[np.argmax(z)]
        f = lambda p: w0 * np.sin(p[0] * t[m]) / p[0] - z[m]
        om_fit = least_squares(f, [0.7 * N], bounds=(1e-3, 5)).x[0]
        kfit = (om_fit / N) ** 2
        tstall = t[np.argmax(z)]
        print(f"  N2={N2}: max depth {z.max():.3f} at t={tstall:.2f}; fitted omega/N={om_fit/N:.3f} "
              f"(kappa_fit={kfit:.3f}); oval predicts stall at t={np.pi/2/(np.sqrt(0.4536)*N):.2f}, "
              f"depth {w0/(np.sqrt(0.4536)*N):.3f}")
        for tt in (1.0, 2.0, 3.0):
            i = np.argmin(abs(t - tt))
            print(f"     t={tt}: deficit sim {dz[i]:.3f}  oval {out[0][i]:.3f}  kappa=1 {out[1][i]:.3f}"
                  f"   gam_core {r['gam_core'][i]:.3f} imp {r['imp'][i]:.3f}")
