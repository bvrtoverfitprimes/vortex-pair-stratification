import json, os
import numpy as np
from scipy.signal import savgol_filter

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")


def load(n):
    return json.load(open(os.path.join(R, n + ".out.json")))


def w0_of(r):
    t = np.array(r["t"]); z = np.array(r["zc"]); m = (t > 0.5) & (t < 3)
    return np.polyfit(t[m], z[m], 1)[0]


def speed_depth(r):
    t = np.array(r["t"]); z = np.array(r["zc"])
    w = savgol_filter(z, 11, 3, deriv=1, delta=t[1] - t[0])
    bad = np.where(np.maximum.accumulate(z) > z + 1e-3)[0]
    i = bad[0] if len(bad) else len(z)
    return z[:i], w[:i]


def Vcurve(neu, run, zq, off=0.0):
    zn, wn = speed_depth(neu); z, w = speed_depth(run)
    return (np.interp(zq + off, zn, wn) ** 2 - np.interp(zq + off, z, w, right=np.nan) ** 2) / 2
