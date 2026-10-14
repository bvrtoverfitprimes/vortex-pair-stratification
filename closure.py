import numpy as np

KAPPA_OVAL = 0.45360470763608335
H_OVAL = np.sqrt(3) / 2


def oval_kernel(n=2001):
    import os
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "oval_kernel.npy")
    yy, K = np.load(p)
    return yy, K


class Kernel:

    def __init__(self, yy=None, K=None, local=False):
        self.local = local
        if not local:
            if yy is None:
                yy, K = oval_kernel()
            self.yy, self.K = yy, K / np.trapezoid(K, yy)
            self.h = yy.max()

    def G(self, z, s):
        z = np.asarray(z, float); s = np.asarray(s, float)
        if self.local:
            return np.where(s > 0, np.maximum(z - s, 0.0), 0.0)
        if not hasattr(self, "_Phi"):
            from scipy.integrate import cumulative_trapezoid
            self._Phi = cumulative_trapezoid(self.K, self.yy, initial=0.0)
            self._M1 = cumulative_trapezoid(self.K * self.yy, self.yy, initial=0.0)
        Z, S = np.broadcast_arrays(z, s)
        a = np.clip(S - Z, -self.h, self.h)
        b = np.clip(S, -self.h, self.h)
        Pa = np.interp(a, self.yy, self._Phi); Pb = np.interp(b, self.yy, self._Phi)
        Ma = np.interp(a, self.yy, self._M1); Mb = np.interp(b, self.yy, self._M1)
        out = (Z - S) * (Pb - Pa) + (Mb - Ma)
        return np.where(b > a, np.maximum(out, 0.0), 0.0)


def layer_grid(a, b, ns, ker=None):
    L = np.linspace(a, b, ns)
    if getattr(ker, "local", False) and a <= 0.0 < b:
        L[np.searchsorted(L, 0.0)] = 1e-12
    return L


def exit_time(V, zgrid, kappa):
    arg = 1.0 - 2.0 * kappa * V
    if np.any(arg[:-1] <= 0):
        return np.inf
    arg = np.maximum(arg, 0.0)
    g = np.sqrt(arg)
    dz = np.diff(zgrid)
    return float(np.sum(2 * dz / (g[:-1] + g[1:])))


def V_atoms(ker, zgrid, positions, masses):
    V = np.zeros_like(zgrid)
    for s, n in zip(positions, masses):
        V += n * ker.G(zgrid, s)
    return V


class TabKernel:

    def __init__(self, zgrid, sgrid, Gtab):
        from scipy.interpolate import RegularGridInterpolator
        self.zg, self.sg, self.Gt = np.asarray(zgrid), np.asarray(sgrid), np.asarray(Gtab)
        self._f = RegularGridInterpolator((self.zg, self.sg), self.Gt, bounds_error=False, fill_value=0.0)
        self.local = False

    def G(self, z, s):
        Z, S = np.broadcast_arrays(np.asarray(z, float), np.asarray(s, float))
        pts = np.stack([np.clip(Z, self.zg[0], self.zg[-1]).ravel(), S.ravel()], axis=1)
        return self._f(pts).reshape(Z.shape)
