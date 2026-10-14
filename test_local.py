import numpy as np
from closure import Kernel, KAPPA_OVAL
from worst import worst, level_range
from check_local import closed_form

ker = Kernel(local=True)
K1 = 0.55
mx = 0.0
for D in (0.5, 1.0, 1.4):
    for dl in (0.5, 1.0):
        x0, xM = level_range(D, dl, "local")
        levels = np.arange(x0, xM + 1e-9, dl)
        for bg in (0.1, 0.25):
            for inv, where in ((0, "-"), (1, "below"), (1, "above"), (2, "below"), (2, "above")):
                masses = bg * np.diff(levels)
                if inv:
                    k0 = np.searchsorted(levels, 0.0, side="right") - 1 - (1 if where == "above" else 0)
                    masses = masses.copy(); masses[k0] += inv * K1
                Tw, _ = worst(ker, KAPPA_OVAL, levels, masses, D)
                cf = closed_form(levels, masses, D)
                rel = abs(Tw - cf) / cf if np.isfinite(cf) and np.isfinite(Tw) else (0.0 if Tw == cf else np.inf)
                mx = max(mx, rel)
                print(D, dl, bg, inv, where, f"{Tw:.6f} {cf:.6f} {rel:.1e}")
print("max rel", mx)
