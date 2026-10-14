# vortex-pair-stratification

Two-dimensional simulations of a descending vortex pair in stratified fluid, the response of its descent to thin
stable layers, and worst-case exit times of the pair from a depth range when the stratification is known only at
discrete levels.

Units: initial spacing 1, point-vortex descent speed 1. Depth is measured downward from the starting level.

## Requirements

Python 3.11 or later with the packages in `requirements.txt`.

```
pip install -r requirements.txt
```

## Files

| File | Purpose |
|---|---|
| `dns2d.py` | Pseudo-spectral Boussinesq solver (doubly periodic, RK4, 2/3 dealiasing) for a Lamb-Oseen vortex pair |
| `runbatch.sh` | Runs several configurations from `runs/` in parallel |
| `oval.py` | Shape of the fluid oval carried by a point-vortex pair; writes `oval_kernel.npy` |
| `closure.py` | Local and oval response kernels, tabulated kernels, exit-time quadrature |
| `diagnostics.py` | Speed-depth curves and energy deficits of runs |
| `build_kernel.py` | Measured response kernel from the thin-layer runs; writes `runs/kernel_dns.npz` |
| `analyze_layers.py` | Closure and P2P-type predictions for single thin layers |
| `analyze_uniform.py` | Uniform-stratification runs against the closures |
| `worst.py` | Worst-case exit times over profiles consistent with level data |
| `prob.py` | Worst-case stall probabilities (Cantelli and semidefinite bounds) |
| `voi.py` | Asymptotic gain from uniform and optimal level placement |
| `verify_reduction.py` | Random instances: one-inversion-per-layer reduction against a global search |
| `check_local.py`, `test_local.py`, `test_interp.py` | Local-kernel worst cases against the closed form |
| `bg_check.py`, `robust_check.py`, `p2p_check.py` | Superposition, robustness, and closure comparisons |

## Data

`runs/` holds every simulation configuration (`NAME.json`) and its output (`NAME.out.json`: time, depth,
half-spacing, core circulation, half-plane impulse), the measured kernel `kernel_dns.npz`, the worst-case results
`worst.txt`, and the verification results `verify_*.json`.

Run prefixes: `L_` thin layers, `K_` kernel layers, `B_` uniform backgrounds with and without a layer, `W_` wide
box, `R_` fine grid, `C_` thin core, `X_` stratification switched on at t = 1, `u_` and `n_` uniform and neutral
runs.

## Reproduction

```
./runbatch.sh 4 L_neutral K_s+0.30
python oval.py
python build_kernel.py
python worst.py > runs/worst.txt
python check_local.py
python voi.py --check
python verify_reduction.py 101 20
```
