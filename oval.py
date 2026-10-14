import numpy as np
from scipy.optimize import brentq
a = 0.5; G = 2*np.pi; U = G/(4*np.pi*a)
def psi(x, y):
    return (G/(4*np.pi))*np.log(((x-a)**2+y**2)/((x+a)**2+y**2)) + U*x
ys = np.sqrt(G*a/(np.pi*U) - a**2)
print("stagnation half-height y_s =", ys, " (sqrt(3) a =", np.sqrt(3)*a, ")")
def halfwidth(y):
    f = lambda x: psi(x, y)
    xs = np.linspace(1e-6, 3, 30001); v = f(xs)
    idx = np.where(np.sign(v[:-1]) != np.sign(v[1:]))[0]
    roots = [brentq(f, xs[i], xs[i+1]) for i in idx]
    roots = [r for r in roots if abs(r - a) > 1e-3 or abs(y) > 1e-3]
    return max(roots) if roots else 0.0
yy = np.linspace(-ys, ys, 2001)
w = np.array([2*halfwidth(y) for y in yy])
A = np.trapezoid(w, yy)
print("max full width =", w.max(), " area A =", A, " A/(2 pi b^2) =", A/(2*np.pi))
np.save("oval_kernel.npy", np.vstack([yy, w/A]))
