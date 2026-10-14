import json, glob, os
import numpy as np
from closure import Kernel

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
ov, lo = Kernel(), Kernel(local=True)


def profile_density(cfg, s):
    d = np.zeros_like(s)
    for n2, top, bot, ew in cfg["layers"]:
        d += n2 * 0.5 * (np.tanh((s - top) / ew) - np.tanh((s - bot) / ew))
    return d + cfg.get("N2_uniform", 0.0)


def model_traj(ker, kappa, cfg, w0, T, zmax=4.0):
    ss = np.linspace(-1.0, zmax + 1.0, 3001)
    dens = profile_density(cfg, ss)
    zg = np.linspace(0, zmax, 1601)
    Gm = ker.G(zg[None, :], ss[:, None])
    V = np.trapezoid(Gm * dens[:, None], ss, axis=0)
    arg = w0**2 - 2 * kappa * V
    stall = np.argmax(arg <= 0) if np.any(arg <= 0) else None
    g = np.sqrt(np.maximum(arg, 0))
    tz = np.concatenate([[0], np.cumsum(2 * np.diff(zg) / (g[:-1] + g[1:] + 1e-300))])
    if stall is not None:
        tz[stall:] = np.inf
    return zg, tz


def p2p_traj(cfg, w0, T=8.0, dt=1e-3):
    tstar = 0.0; z = 0.0; G = 1.0; Nbar = 0.0
    dts = dt * w0
    zs, ts = [0.0], [0.0]
    while tstar < T * w0:
        N2 = profile_density(cfg, np.array([z]))[0]
        Nstar = np.sqrt(max(N2, 0.0)) / w0
        Nbar = (tstar * Nbar + dts * Nstar) / (tstar + dts)
        G -= dts * 0.4525 * Nbar ** np.sqrt(2.0) * z
        z += dts * G
        tstar += dts
        if G <= 0:
            break
        zs.append(z); ts.append(tstar / w0)
    zs, ts = np.array(zs), np.array(ts)
    zg = np.linspace(0, 4.0, 1601)
    tz = np.interp(zg, zs, ts, right=np.inf)
    return zg, tz


def first_time(t, z, D):
    i = np.argmax(np.asarray(z) >= D)
    if z[i] < D:
        return np.inf
    return np.interp(D, [z[i - 1], z[i]], [t[i - 1], t[i]])


if __name__ == "__main__":
    neu = json.load(open(os.path.join(R, "L_neutral.out.json")))
    tn, zn = np.array(neu["t"]), np.array(neu["zc"])
    w0 = np.polyfit(tn[(tn > 0.5) & (tn < 3)], zn[(tn > 0.5) & (tn < 3)], 1)[0]
    print(f"neutral w0 = {w0:.4f}")
    rows = []
    for f in sorted(glob.glob(os.path.join(R, "L_n*.out.json"))):
        r = json.load(open(f)); cfg = r["cfg"]
        t, z = np.array(r["t"]), np.array(r["zc"])
        name = os.path.basename(f).replace(".out.json", "")
        out = [name]
        for D in (0.5, 1.0, 1.5, 2.0):
            ts = first_time(t, z, D)
            tn_D = first_time(tn, zn, D)
            preds = []
            for ker, kap in ((lo, 1.0), (lo, 0.4536), (ov, 0.4536), (ov, 1.0)):
                zg, tz = model_traj(ker, kap, cfg, w0, 4.0)
                preds.append(np.interp(D, zg, tz))
            rows.append((name, D, ts, tn_D, *preds))
            out.append(f"D={D}: sim {ts - tn_D:+.3f} | locK1 {preds[0] - D/w0:+.3f} locK.45 {preds[1] - D/w0:+.3f} "
                       f"ovK.45 {preds[2] - D/w0:+.3f} ovK1 {preds[3] - D/w0:+.3f}")
        print("\n  ".join(out))
    json.dump(rows, open(os.path.join(R, "layer_rows.json"), "w"), default=float)
