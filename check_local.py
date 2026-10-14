import os
import numpy as np
from closure import KAPPA_OVAL
from worst import level_range

K1 = 0.55
HERE = os.path.dirname(os.path.abspath(__file__))


def closed_form(levels, masses, D, kap=KAPPA_OVAL):
    xi = np.unique(np.concatenate([[0.0, D], levels[(levels > 0) & (levels < D)]]))
    def E(z):
        return sum(n * max(z - max(levels[k], 0.0), 0.0) for k, n in enumerate(masses) if levels[k + 1] > 0)
    g = np.array([1 - 2 * kap * E(x) for x in xi])
    if np.any(g[:-1] <= 0) or g[-1] < 0:
        return np.inf
    g = np.sqrt(g)
    return float(np.sum(2 * np.diff(xi) / (g[:-1] + g[1:])))


def main():
    maxrel = 0.0
    worst_rows = [l for l in open(os.path.join(HERE, "runs", "worst.txt")) if l.startswith("D=")]
    for line in worst_rows:
        head = line.split(":")[0].split()
        D, dl, bg = float(head[0][2:]), float(head[1][3:]), float(head[2][5:])
        inv = int(head[3][4])
        where = head[4] if len(head) > 4 else "-"
        x0, xM = level_range(D, dl)
        levels = np.arange(x0, xM + 1e-9, dl)
        masses = bg * np.diff(levels)
        if inv:
            k0 = np.searchsorted(levels, 0.0, side="right") - 1 - (1 if where == "above" else 0)
            masses = masses.copy(); masses[k0] += inv * K1
        cf = closed_form(levels, masses, D)
        tab = float(line.split("local:")[1].split("worst")[1].split()[0])
        if np.isfinite(cf) or np.isfinite(tab):
            rel = abs(tab - cf) / cf if np.isfinite(cf) and np.isfinite(tab) else np.inf
            maxrel = max(maxrel, rel)
            flag = "" if abs(tab - cf) <= 5e-4 else "  <-- MISMATCH"
            print(f"{line.split(':')[0]:40s} table {tab:.6f} closed {cf:.6f}{flag}")
        else:
            print(f"{line.split(':')[0]:40s} both stall")
    print("max relative difference", maxrel)


if __name__ == "__main__":
    main()
