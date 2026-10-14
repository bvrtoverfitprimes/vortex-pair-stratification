import glob, json, os
import numpy as np
from scipy.signal import savgol_filter

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
ZMAX = 1.6
zq = np.linspace(0.0, ZMAX, 81)


def speed_depth(r):
    t = np.array(r["t"]); z = np.array(r["zc"])
    w = savgol_filter(z, 11, 3, deriv=1, delta=t[1] - t[0])
    run_max = np.maximum.accumulate(z)
    bad = np.where(run_max > z + 1e-3)[0]
    i = bad[0] if len(bad) else len(z)
    return z[:i], w[:i]


def main():
    neu = json.load(open(os.path.join(R, "L_neutral.out.json")))
    zn, wn = speed_depth(neu)
    wnq = np.interp(zq, zn, wn)
    wnq[0] = wnq[1]
    rows = []
    for f in sorted(glob.glob(os.path.join(R, "K_s*.out.json"))):
        r = json.load(open(f))
        n2, top, bot, ew = r["cfg"]["layers"][0]
        n = n2 * (bot - top); s = 0.5 * (top + bot)
        z, w = speed_depth(r)
        wq = np.interp(zq, z, w, right=np.nan)
        G = (wnq**2 - wq**2) / 2 / n
        G[0] = 0.0
        rows.append((s, G))
    rows.sort(key=lambda x: x[0])
    sg = np.array([s for s, _ in rows]); Gt = np.array([G for _, G in rows]).T
    np.savez(os.path.join(R, "kernel_dns.npz"), z=zq, s=sg, G=Gt)
    print("s grid:", np.round(sg, 3))
    for j in range(0, len(zq), 10):
        print(f"z={zq[j]:.2f}: " + " ".join(f"{g:+.3f}" for g in Gt[j]))


if __name__ == "__main__":
    main()
