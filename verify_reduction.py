import json, sys
import numpy as np
from scipy.optimize import differential_evolution, minimize_scalar
from closure import Kernel, exit_time, KAPPA_OVAL

ker = Kernel()
NZ = 801


def T_of(levels, masses, pos, wts, D, kappa):
    zg = np.linspace(0, D, NZ)
    V = np.zeros(NZ)
    for k, n in enumerate(masses):
        for s, w in zip(pos[k], wts[k]):
            V += n * w * ker.G(zg, s)
    return exit_time(V, zg, kappa)


def reduction(levels, masses, D, kappa, ngrid=161):
    M = len(masses)
    zg = np.linspace(0, D, NZ)
    fixed, active = {}, []
    for k in range(M):
        a, b = levels[k], levels[k + 1]
        if b <= 0:
            fixed[k] = b
        elif a >= D / 2:
            fixed[k] = a
        else:
            active.append(k)
    Vfix = sum(masses[k] * ker.G(zg, s) for k, s in fixed.items()) if fixed else np.zeros(NZ)
    grids = {k: np.linspace(max(levels[k], 0.0) if levels[k] < 0 else levels[k],
                            min(levels[k + 1], D / 2) if levels[k + 1] > D / 2 else levels[k + 1], ngrid)
             for k in active}
    pos = {k: grids[k][len(grids[k]) // 2] for k in active}
    Gt = {k: ker.G(zg[None, :], grids[k][:, None]) for k in active}
    best = None
    for _ in range(8):
        changed = False
        for k in active:
            Vrest = Vfix + sum(masses[j] * ker.G(zg, pos[j]) for j in active if j != k)
            Ts = [exit_time(Vrest + masses[k] * Gt[k][i], zg, kappa) for i in range(len(grids[k]))]
            i = int(np.argmax(Ts))
            lo_, hi_ = grids[k][max(i - 1, 0)], grids[k][min(i + 1, len(grids[k]) - 1)]
            f = lambda s: -exit_time(Vrest + masses[k] * ker.G(zg, s), zg, kappa)
            r = minimize_scalar(f, bounds=(lo_, hi_), method="bounded", options={"xatol": 1e-10})
            s_new = r.x if -r.fun >= Ts[i] else grids[k][i]
            if abs(s_new - pos[k]) > 1e-12:
                pos[k], changed = s_new, True
        if not changed:
            break
    V = Vfix + sum(masses[k] * ker.G(zg, pos[k]) for k in active)
    allpos = {**fixed, **pos}
    return exit_time(V, zg, kappa), [allpos[k] for k in range(M)]


def search(levels, masses, D, kappa, seed, natoms=3):
    M = len(masses)
    def unpack(x):
        pos, wts = [], []
        for k in range(M):
            p = x[k * 2 * natoms: k * 2 * natoms + natoms]
            w = np.abs(x[k * 2 * natoms + natoms: (k + 1) * 2 * natoms]) + 1e-12
            pos.append(levels[k] + p * (levels[k + 1] - levels[k])); wts.append(w / w.sum())
        return pos, wts
    def f(x):
        pos, wts = unpack(x)
        T = T_of(levels, masses, pos, wts, D, kappa)
        return -T if np.isfinite(T) else -1e6
    bounds = [(0, 1)] * natoms + [(0, 1)] * natoms
    r = differential_evolution(f, bounds * M, seed=seed, popsize=20, maxiter=300, tol=1e-12,
                               polish=False)
    return -r.fun


if __name__ == "__main__":
    seed = int(sys.argv[1]); ntrial = int(sys.argv[2])
    rng = np.random.default_rng(seed)
    rows = []
    for trial in range(ntrial):
        M = int(rng.integers(2, 5))
        D = float(rng.uniform(0.5, 2.0))
        inner = np.sort(rng.uniform(-0.6, D + 0.6, M - 1))
        levels = np.concatenate([[-1.0], inner, [D + 1.0]])
        masses = rng.dirichlet(np.ones(M)) * rng.uniform(0.2, 2.0)
        kappa = KAPPA_OVAL
        zg = np.linspace(0, D, NZ)
        S = sum(masses[k] * ker.G(zg[None, :], np.linspace(levels[k], levels[k + 1], 201)[:, None]).max(axis=0)
                for k in range(M))
        if np.any(2 * kappa * S[:-1] >= 1):
            rows.append(dict(seed=seed, trial=trial, M=M, D=D, levels=levels.tolist(), masses=masses.tolist(),
                             stall=True))
            continue
        Tred, pos = reduction(levels, masses, D, kappa)
        Ts = max(search(levels, masses, D, kappa, s) for s in (0, 1))
        rows.append(dict(seed=seed, trial=trial, M=M, D=D, levels=levels.tolist(), masses=masses.tolist(),
                         stall=False, Tred=Tred, Tsearch=Ts, diff=Ts - Tred, pos=pos))
        print(f"{seed} {trial} M={M} D={D:.3f} Tred={Tred:.6f} Tsrch={Ts:.6f} diff={Ts-Tred:+.2e}", flush=True)
    json.dump(rows, open(f"runs/verify_{seed}.json", "w"))
