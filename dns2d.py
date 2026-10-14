import argparse, json, time
import numpy as np
from scipy import fft as sfft


def build(Lx, Lz, nx, nz):
    x = (np.arange(nx) - nx // 2) * (Lx / nx)
    z = (np.arange(nz)) * (Lz / nz)
    kx = 2 * np.pi * sfft.rfftfreq(nx, d=Lx / nx)
    kz = 2 * np.pi * sfft.fftfreq(nz, d=Lz / nz)
    KX, KZ = np.meshgrid(kx, kz)
    K2 = KX**2 + KZ**2
    iK2 = np.where(K2 > 0, 1.0 / np.where(K2 > 0, K2, 1), 0.0)
    dealias = (np.abs(KX) < (2 / 3) * kx.max()) & (np.abs(KZ) < (2 / 3) * np.abs(kz).max())
    return x, z, KX, KZ, K2, iK2, dealias


def run(cfg):
    Lx, Lz, nx, nz = cfg["Lx"], cfg["Lz"], cfg["nx"], cfg["nz"]
    nu, kap, rc = cfg["nu"], cfg["kappa"], cfg["rc"]
    z0 = cfg["z0"]
    x, z, KX, KZ, K2, iK2, dea = build(Lx, Lz, nx, nz)
    X, Z = np.meshgrid(x, z)
    depth = (z0 - cfg.get("layer_offset", 0.0)) - Z
    N2 = np.zeros_like(Z)
    for lay in cfg["layers"]:
        n2, dt_, db_, ew = lay
        N2 += n2 * 0.5 * (np.tanh((depth - dt_) / ew) - np.tanh((depth - db_) / ew))
    N2 += cfg.get("N2_uniform", 0.0)
    G = 2 * np.pi
    a = 0.5
    om = np.zeros_like(Z)
    for sx, sg in ((a, 1.0), (-a, -1.0)):
        for ix in (-1, 0, 1):
            for iz in (-1, 0, 1):
                r2 = (X - sx - ix * Lx) ** 2 + (Z - z0 - iz * Lz) ** 2
                om += sg * G / (np.pi * rc**2) * np.exp(-r2 / rc**2)
    b = np.zeros_like(Z)
    omh = sfft.rfft2(om, workers=cfg.get("workers", 1))
    bh = sfft.rfft2(b, workers=cfg.get("workers", 1))
    W = cfg.get("workers", 1)
    lapnu = -nu * K2
    lapka = -kap * K2

    t_on = cfg.get("N2_on_time", 0.0)
    N2full = N2.copy()

    def rhs(omh, bh):
        psih = omh * iK2
        u = sfft.irfft2(1j * KZ * psih, s=(nz, nx), workers=W)
        w = sfft.irfft2(-1j * KX * psih, s=(nz, nx), workers=W)
        omx = sfft.irfft2(1j * KX * omh, s=(nz, nx), workers=W)
        omz = sfft.irfft2(1j * KZ * omh, s=(nz, nx), workers=W)
        bx = sfft.irfft2(1j * KX * bh, s=(nz, nx), workers=W)
        bz = sfft.irfft2(1j * KZ * bh, s=(nz, nx), workers=W)
        nom = -(u * omx + w * omz)
        nb = -(u * bx + w * bz) - (N2full if t_cur[0] >= t_on else 0.0) * w
        r_om = dea * sfft.rfft2(nom, workers=W) + 1j * KX * bh + lapnu * omh
        r_b = dea * sfft.rfft2(nb, workers=W) + lapka * bh
        return r_om, r_b, u, w

    dx = Lx / nx
    t, T = 0.0, cfg["T"]
    t_cur = [0.0]
    dt = cfg["dt"]
    out = {"t": [], "zc": [], "xc": [], "gam_core": [], "gam_half": [], "imp": [], "umax": []}
    mask_r = x > 0
    next_out, dout = 0.0, cfg["dout"]
    t_start = time.time()
    while t <= T + 1e-12:
        if t >= next_out - 1e-12:
            om = sfft.irfft2(omh, s=(nz, nx), workers=W)
            right = om[:, mask_r]
            Xr, Zr = X[:, mask_r], Z[:, mask_r]
            thr = 0.2 * right.max()
            wgt = np.where(right > thr, right, 0.0)
            zc = (wgt * Zr).sum() / wgt.sum()
            xc = (wgt * Xr).sum() / wgt.sum()
            rr = np.sqrt((Xr - xc) ** 2 + (Zr - zc) ** 2)
            gcore = (right * (rr < cfg.get("r_core", 0.5))).sum() * dx * dx
            ghalf = right.sum() * dx * dx
            imp = (Xr * right).sum() * dx * dx
            out["t"].append(t); out["zc"].append(z0 - zc); out["xc"].append(xc)
            out["gam_core"].append(gcore / G); out["gam_half"].append(ghalf / G)
            out["imp"].append(imp / (G * a)); out["umax"].append(float(np.abs(om).max()))
            next_out += dout
            if abs(t / 0.5 - round(t / 0.5)) < 1e-9:
                print(f"progress t={t:.2f} z={z0 - zc:.3f} wall={time.time() - t_start:.0f}s", flush=True)
        t_cur[0] = t
        k1o, k1b, u, w = rhs(omh, bh)
        k2o, k2b, _, _ = rhs(omh + 0.5 * dt * k1o, bh + 0.5 * dt * k1b)
        k3o, k3b, _, _ = rhs(omh + 0.5 * dt * k2o, bh + 0.5 * dt * k2b)
        k4o, k4b, _, _ = rhs(omh + dt * k3o, bh + dt * k3b)
        omh = omh + dt / 6 * (k1o + 2 * k2o + 2 * k3o + k4o)
        bh = bh + dt / 6 * (k1b + 2 * k2b + 2 * k3b + k4b)
        t += dt
        if not np.isfinite(omh[0, 0]):
            raise RuntimeError("blow-up")
    out["wall_s"] = time.time() - t_start
    out["cfg"] = cfg
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cfg")
    ap.add_argument("out")
    a = ap.parse_args()
    cfg = json.load(open(a.cfg))
    res = run(cfg)
    json.dump(res, open(a.out, "w"))
    print("done", a.out, res["wall_s"])
