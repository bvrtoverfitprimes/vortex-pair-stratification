import sys
import numpy as np
from worst import load_kernels, level_range, worst
from closure import layer_grid

K1 = 0.55


class Shift:
    def __init__(self, ker, d):
        self.ker, self.d, self.local = ker, d, False

    def G(self, z, s):
        return self.ker.G(z, s) + self.d


ker, kap = load_kernels()["dns"]
for eps in [float(a) for a in sys.argv[1:]] or [0.023]:
    counts = {"stall": 0, "safe": 0, "undecided": 0}
    widths = []
    for D in (0.5, 1.0, 1.4):
        for dl in (0.5, 1.0):
            x0, xM = level_range(D, dl)
            levels = np.arange(x0, xM + 1e-9, dl)
            for bg in (0.1, 0.25):
                for inv, where in ((0, "-"), (1, "below"), (1, "above"), (2, "below"), (2, "above")):
                    masses = bg * np.diff(levels)
                    if inv:
                        k0 = np.searchsorted(levels, 0.0, side="right") - 1 - (1 if where == "above" else 0)
                        masses = masses.copy(); masses[k0] += inv * K1
                    zg = np.linspace(0, D, 321)
                    S = sum(n * kap * ker.G(zg[None, :], layer_grid(levels[k], levels[k + 1], 121, ker)[:, None]).max(axis=0)
                            for k, n in enumerate(masses))
                    m = S[:-1].max()
                    cls = "stall" if m - eps > 0.5 else ("safe" if m + eps < 0.5 else "undecided")
                    counts[cls] += 1
                    lo = hi = np.inf
                    if cls != "stall":
                        nb = masses.sum()
                        lo, _ = worst(Shift(ker, -eps / nb), kap, levels, masses, D, ns=61, sweeps=6)
                        hi, _ = worst(Shift(ker, eps / nb), kap, levels, masses, D, ns=61, sweeps=6)
                        if np.isfinite(hi):
                            widths.append((hi - lo) / D)
                    print(f"eps={eps} D={D} dl={dl} bg={bg} {inv}K {where:5s} maxS={m:.3f} {cls:9s} "
                          f"T* in [{lo:.3f}, {hi:.3f}]", flush=True)
    print(f"eps={eps}: {counts}; bracket width / D: max {max(widths):.3f}, median {np.median(widths):.3f}")
