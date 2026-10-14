import numpy as np
from closure import Kernel, KAPPA_OVAL, exit_time
from worst import interp_T, level_range

ker = Kernel(local=True); kap = KAPPA_OVAL; K1 = 0.55


def exact_V(levels, masses, zg):
    V = np.zeros_like(zg)
    for k, n in enumerate(masses):
        a, b = max(levels[k], 0.0), levels[k + 1]
        if b <= 0:
            continue
        lo = np.minimum(zg, a); hi = np.minimum(zg, b)
        V += kap * n / (levels[k + 1] - levels[k]) * np.where(zg > a, 0.5 * ((zg - lo) ** 2 - (zg - hi) ** 2), 0.0)
    return V


mx = 0.0
for D in (0.5, 1.0, 1.4):
    for dl in (0.5, 1.0):
        x0, xM = level_range(D, dl, "local")
        levels = np.arange(x0, xM + 1e-9, dl)
        for bg in (0.1, 0.25):
            for inv, where in ((0, "-"), (1, "below"), (2, "below"), (2, "above")):
                masses = bg * np.diff(levels)
                if inv:
                    k0 = np.searchsorted(levels, 0.0, side="right") - 1 - (1 if where == "above" else 0)
                    masses = masses.copy(); masses[k0] += inv * K1
                Ti = interp_T(ker, kap, levels, masses, D)
                zf = np.linspace(0, D, 20001)
                Te = exit_time(exact_V(levels, masses, zf), zf, 1.0)
                rel = abs(Ti - Te) / Te if np.isfinite(Te) else 0.0
                mx = max(mx, rel)
                print(D, dl, bg, inv, where, f"{Ti:.6f} {Te:.6f} {rel:.1e}")
print("max rel", mx)
