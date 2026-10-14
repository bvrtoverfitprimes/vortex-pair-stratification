import numpy as np
import cvxpy as cp
from closure import layer_grid


def g_matrix(ker, levels, zgrid, ns=201):
    M = len(levels) - 1
    g = np.zeros((len(zgrid), M))
    for k in range(M):
        ss = layer_grid(levels[k], levels[k + 1], ns, ker)
        g[:, k] = ker.G(zgrid[:, None], ss[None, :]).max(axis=1)
    return g


def cantelli_lower(g, c, m, Sigma):
    best, arg = 0.0, None
    for i, a in enumerate(g):
        mu, var = a @ m, a @ Sigma @ a
        p = 1.0 if mu >= c else var / (var + (c - mu) ** 2)
        if p > best:
            best, arg = p, i
    return best, arg


def vbc_upper(A, b, m, Sigma, solver="CLARABEL"):
    n = len(m)
    S = Sigma + np.outer(m, m)
    Mtot = np.block([[S, m[:, None]], [m[None, :], np.ones((1, 1))]])
    blocks, lams, cons = [], [], []
    tot = 0
    for i in range(A.shape[0]):
        P = cp.Variable((n + 1, n + 1), PSD=True)
        z = P[:n, n]; lam = P[n, n]
        cons.append(A[i] @ z >= b[i] * lam)
        tot = tot + P
        lams.append(lam)
    cons.append(Mtot - tot >> 0)
    prob = cp.Problem(cp.Maximize(sum(lams)), cons)
    prob.solve(solver=solver)
    return float(prob.value), prob.status


if __name__ == "__main__":
    from closure import Kernel, KAPPA_OVAL
    ov, lo = Kernel(), Kernel(local=True)
    D = 1.0; dl = 0.5
    levels = np.arange(-1.0, D + 1.0 + 1e-9, dl)
    M = len(levels) - 1
    zg = np.linspace(0, D, 41)[1:]
    K1 = 0.55
    m = 0.25 * np.diff(levels)
    k0 = np.searchsorted(levels, 0.0, side="right") - 1
    for mean_K, sd_K in ((1.0, 0.5), (2.0, 1.0), (3.0, 1.0)):
        mm = m.copy(); mm[k0] += mean_K * K1
        Sig = np.diag((0.3 * m) ** 2); Sig[k0, k0] += (sd_K * K1) ** 2
        for name, ker in (("oval", ov), ("local", lo)):
            kap = KAPPA_OVAL
            g = kap * g_matrix(ker, levels, zg)
            c = 0.5
            pl, _ = cantelli_lower(g, c, mm, Sig)
            pu, st = vbc_upper(g, np.full(len(zg), c), mm, Sig)
            print(f"inversion forecast {mean_K} K +- {sd_K} K, {name:5s}: sup P(stall) in [{pl:.4f}, {pu:.4f}] ({st})")
