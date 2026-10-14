import os
import numpy as np
from closure import Kernel, TabKernel, exit_time, layer_grid, KAPPA_OVAL

HERE = os.path.dirname(os.path.abspath(__file__))


def load_kernels():
    ks = {"local": (Kernel(local=True), KAPPA_OVAL), "oval": (Kernel(), KAPPA_OVAL)}
    p = os.path.join(HERE, "runs", "kernel_dns.npz")
    if os.path.exists(p):
        d = np.load(p)
        ks["dns"] = (TabKernel(d["z"], d["s"], d["G"]), 1.0)
    return ks


def level_range(D, step, name=None):
    if name in (None, "dns") and os.path.exists(os.path.join(HERE, "runs", "kernel_dns.npz")):
        sk = np.load(os.path.join(HERE, "runs", "kernel_dns.npz"))["s"]
        return -1.0, max(D + 1.0, step * np.ceil((sk[-1] + 0.075) / step - 1e-9))
    return -1.0, D + 1.0


def worst(ker, kap, levels, masses, D, nz=321, ns=121, sweeps=10):
    zg = np.linspace(0, D, nz)
    M = len(masses)
    Ls = [layer_grid(levels[k], levels[k + 1], ns, ker) for k in range(M)]
    Gt = [kap * ker.G(zg[None, :], L[:, None]) for L in Ls]
    S = sum(n * g.max(axis=0) for n, g in zip(masses, Gt))
    if np.any(2 * S[:-1] >= 1):
        return np.inf, None
    best_T, best_idx = -1, None
    for start in (0, ns - 1, ns // 2):
        idx = [start] * M
        def T_of(ix): return exit_time(sum(masses[k] * Gt[k][ix[k]] for k in range(M)), zg, 1.0)
        T = T_of(idx)
        for _ in range(sweeps):
            changed = False
            for k in range(M):
                if masses[k] == 0:
                    continue
                Vrest = sum(masses[j] * Gt[j][idx[j]] for j in range(M) if j != k)
                Ts = np.array([exit_time(Vrest + masses[k] * Gt[k][i], zg, 1.0) for i in range(ns)])
                i = int(np.argmax(Ts))
                if Ts[i] > T + 1e-13:
                    T, idx[k], changed = Ts[i], i, True
            if not changed:
                break
        if T > best_T:
            best_T, best_idx = T, list(idx)
    return best_T, [Ls[k][best_idx[k]] for k in range(M)]


def interp_T(ker, kap, levels, masses, D, nz=641, ns=4000):
    zg = np.linspace(0, D, nz)
    V = np.zeros(nz)
    for k, n in enumerate(masses):
        e = np.linspace(levels[k], levels[k + 1], ns + 1)
        ss = 0.5 * (e[1:] + e[:-1])
        V += n * kap * ker.G(zg[None, :], ss[:, None]).mean(axis=0)
    return exit_time(V, zg, 1.0)


if __name__ == "__main__":
    ks = load_kernels()
    K1 = 0.55
    for D in (0.5, 1.0, 1.4):
        for dl in (0.5, 1.0):
            x0, xM = level_range(D, dl)
            levels = np.arange(x0, xM + 1e-9, dl)
            M = len(levels) - 1
            for bg in (0.1, 0.25):
                for inv_K, where in ((0, "-"), (1, "below"), (1, "above"), (2, "below"), (2, "above")):
                    if inv_K == 0 and where != "-":
                        continue
                    masses = bg * np.diff(levels)
                    if inv_K:
                        k0 = np.searchsorted(levels, 0.0, side="right") - 1
                        if where == "above":
                            k0 -= 1
                        masses = masses.copy(); masses[k0] += inv_K * K1
                    line = f"D={D} dl={dl} N*^2={bg} inv={inv_K}K {where:5s}:"
                    for name, (ker, kap) in ks.items():
                        Ti = interp_T(ker, kap, levels, masses, D)
                        Tw, pos = worst(ker, kap, levels, masses, D)
                        line += f"  {name}: interp {Ti:.3f} worst {Tw:.3f}"
                    print(line, flush=True)
