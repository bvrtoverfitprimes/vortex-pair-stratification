import sys
import numpy as np
from worst import load_kernels, level_range, worst
from closure import exit_time

N2 = 0.25


def voi(ker, kap, D, x0, xM, ns=4001, nz=321):
    zg = np.linspace(0, D, nz)
    ss = np.linspace(x0, xM, ns)
    G = kap * ker.G(zg[:, None], ss[None, :])
    Vs = N2 * np.trapezoid(G, ss, axis=1)
    psi1 = (1 - 2 * Vs) ** -1.5
    Lt = np.trapezoid(psi1[:, None] * G, zg, axis=0)
    Lam = np.gradient(Lt, ss)
    c = N2 * np.abs(Lam)
    uni = 0.5 * (xM - x0) * np.trapezoid(c, ss)
    opt = 0.5 * np.trapezoid(np.sqrt(c), ss) ** 2
    rho = np.sqrt(c) / np.trapezoid(np.sqrt(c), ss)
    return uni, opt, ss, rho, exit_time(Vs, zg, 1.0)


def check(ker, kap, D, x0, xM, M):
    levels = np.linspace(x0, xM, M + 1)
    masses = N2 * np.diff(levels)
    zg = np.linspace(0, D, 321)
    ss = np.linspace(x0, xM, 4001)
    Vs = N2 * np.trapezoid(kap * ker.G(zg[:, None], ss[None, :]), ss, axis=1)
    Tw, _ = worst(ker, kap, levels, masses, D, ns=61, sweeps=6)
    return M * (Tw - exit_time(Vs, zg, 1.0))


if __name__ == "__main__":
    ks = load_kernels()
    for D in (1.0, 1.4):
        for name in ("oval", "dns"):
            ker, kap = ks[name]
            x0, xM = level_range(D, 0.01, name)
            if name == "dns":
                xM = float(np.load("runs/kernel_dns.npz")["s"][-1])
            uni, opt, ss, rho, T0 = voi(ker, kap, D, x0, xM)
            top = ss[1:-1][np.argmax(rho[1:-1])]
            print(f"D={D} {name}: range [{x0:.2f},{xM:.2f}] T={T0:.4f} uniform {uni:.4f} optimal {opt:.4f} "
                  f"ratio {uni/opt:.3f} densest at s={top:+.3f}", flush=True)
            if "--check" in sys.argv:
                for M in (20, 40, 80):
                    print(f"   M={M}: M(T*-T) = {check(ker, kap, D, x0, xM, M):.4f}", flush=True)
