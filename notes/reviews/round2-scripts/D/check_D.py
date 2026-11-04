"""Checks for referee part D: critical values, limit, bounds, Figure 2, shadow of the step,
dictionary examples, and the third open problem (the step exponent in the next dimension)."""
import mpmath as mp
import numpy as np
from scipy import integrate, optimize, special

mp.mp.dps = 30

def M(d):
    m = (d + 1) / 2
    lam = 2 ** (-d / 2)
    h = lambda z: z ** m * (mp.e ** (-z) - lam * mp.e ** (-z / 2))
    # maximise on (0, d log 2)
    hf = lambda z: -float(h(z))
    res = optimize.minimize_scalar(hf, bounds=(1e-9, d * np.log(2)), method="bounded", options={"xatol": 1e-13})
    zstar = mp.mpf(res.x)
    return h(zstar), zstar

def w(d):
    m = (d + 1) / 2
    Md, zs = M(d)
    return mp.gamma(m) / (2 * Md), zs

print("== critical values ==")
for d in [1, 2, 3, 4, 5, 10, 20]:
    wd, zs = w(d)
    print(f"d={d:3d}  w_d={float(wd):.6f}  sqrt(d) w_d={float(mp.sqrt(d)*wd):.6f}  z*={float(zs):.4f}  "
          f"w_d/sqrt(pi/d)={float(wd/mp.sqrt(mp.pi/d)):.3f}")

print("sqrt(pi) =", float(mp.sqrt(mp.pi)))
print("== behaviour of sqrt(d) w_d: crossing below sqrt(pi), minimum ==")
prev = None
vals = {}
for d in range(1, 301):
    wd, _ = w(d)
    vals[d] = float(mp.sqrt(d) * wd)
below = [d for d in range(1, 301) if vals[d] < float(mp.sqrt(mp.pi))]
print("first d with sqrt(d) w_d < sqrt(pi):", below[0] if below else None)
dmin = min(vals, key=vals.get)
print("minimum at d =", dmin, "value", vals[dmin])
print("values at 55,56,81,100,200,300:", [round(vals[k], 5) for k in (55, 56, 81, 100, 200, 300)])
print("monotone increasing after the minimum up to 300:",
      all(vals[d] <= vals[d + 1] for d in range(dmin, 300)))

print("== Lemma A.11 bounds ==")
K = mp.sqrt(mp.pi / 2) + mp.sqrt(mp.pi) + 4
for d in [1, 2, 3, 4, 10, 20]:
    m = (d + 1) / 2
    eps = 2 ** (-d / 2) * mp.e ** (m / 2)
    wd, _ = w(d)
    lower = mp.e ** (-0.5) / (2 * mp.sqrt(m))
    upper = K / (2 * (1 - eps) * mp.sqrt(m)) if eps < 1 else None
    print(f"d={d}: eps_d={float(eps):.4f}  lower={float(lower):.4f}  w_d={float(wd):.4f}  "
          f"upper={'n/a' if upper is None else round(float(upper),4)}  ok={lower <= wd and (upper is None or wd <= upper)}")

print("== Theorem A.15(2): M_2 > 1/15 and w_2 < 7.5 < 6+4 sqrt 2 ==")
M2, _ = M(2)
print("M_2 =", float(M2), "> 1/15 =", 1 / 15, ";  w_2 =", float(w(2)[0]), "; 6+4sqrt2 =", 6 + 4 * 2 ** 0.5)
print("w_1 =", float(w(1)[0]), "> 6+4sqrt2 ?", float(w(1)[0]) > 6 + 4 * 2 ** 0.5)

print("== Figure 2(b): polar profile (A.19) of F^(4) in d=1,2,3 ==")
def k_profile(d, wv, r):
    m = (d + 1) / 2
    return (2 ** 1.5 * special.gamma(m) / special.gamma(d / 2)) / r + 2 * wv * (
        special.gammainc(d / 2, r ** 2 / 2) - special.gammainc(d / 2, r ** 2 / 4))

rs = np.linspace(0.05, 4, 4000)
for d in (1, 2, 3):
    k = k_profile(d, 4.0, rs)
    dk = np.diff(k)
    inc = rs[1:][dk > 0]
    print(f"d={d}: k(0.5)={k_profile(d,4.0,0.5):.3f} k(1)={k_profile(d,4.0,1.0):.3f} k(2)={k_profile(d,4.0,2.0):.3f} k(3)={k_profile(d,4.0,3.0):.3f}",
          "increasing on", (round(inc.min(), 3), round(inc.max(), 3)) if inc.size else "nowhere")
# the predicted rising interval in d=3: 4 h_3(z) > Gamma(2)/2
h3 = lambda z: z ** 2 * (np.exp(-z) - 2 ** -1.5 * np.exp(-z / 2))
zs = np.linspace(0.01, 3, 100000)
mask = 4 * h3(zs) > 0.5
print("predicted rising interval in r for d=3:", (round(np.sqrt(2 * zs[mask].min()), 3), round(np.sqrt(2 * zs[mask].max()), 3)))

print("== shadow of the step b 1_(0,tau) from the plane to the line (Lemma A.8, d=1) ==")
b, tau = 1.0, 1.0
C1 = 2 / (2 * np.pi)
def shadow(r):
    U = np.sqrt(tau ** 2 / r ** 2 - 1)
    val, _ = integrate.quad(lambda u: 1 / (1 + u ** 2), -U, U)
    return C1 * b * val
for r in (0.1, 0.5, 0.9, 0.99):
    print(f"r={r}: shadow={shadow(r):.6f}  (2b/pi) arccos(r/tau)={2*b/np.pi*np.arccos(r/tau):.6f}")
print("normalisation C_d int (1+u^2)^(-(d+1)/2) du for d=1..4:",
      [round(float(special.gamma((d + 1) / 2) / (np.sqrt(np.pi) * special.gamma(d / 2))
                   * integrate.quad(lambda u: (1 + u * u) ** (-(d + 1) / 2), -np.inf, np.inf)[0]), 8) for d in (1, 2, 3, 4)])

print("== dictionary: Matern exponent ==")
g = 1.3
F = lambda r: g * np.log(1 + r * r / 2)
for r in (0.5, 1, 2):
    Fp = (F(r + 1e-6) - F(r - 1e-6)) / 2e-6
    print(f"r={r}: 1 - r F'(r)/(2 gamma) = {1 - r*Fp/(2*g):.6f}, (1+r^2/2)^-1 = {1/(1+r*r/2):.6f}")

print("== Omega_d: mean of cos(t<e,eta>) over the sphere ==")
for t in (0.7, 2.0):
    om2 = integrate.quad(lambda th: np.cos(t * np.cos(th)), 0, 2 * np.pi)[0] / (2 * np.pi)
    om3 = integrate.quad(lambda u: np.cos(t * u), -1, 1)[0] / 2
    print(f"t={t}: Omega_2={om2:.6f} J0={special.j0(t):.6f}; Omega_3={om3:.6f} sin t/t={np.sin(t)/t:.6f}")

print("== Open problem 3: is b Cin(tau|zeta|) the exponent of an ID law in R^2 and R^3? ==")
# R^3: claim  b Cin(tau r) = G_3(r) + b (1 - Omega_3(tau r)),  G_3(r) = b int_0^r (1 - Omega_3(tau u)) du/u
Cin = lambda x: integrate.quad(lambda v: (1 - np.cos(v)) / v, 0, x)[0]
for r in (0.5, 2.0, 7.0):
    G3 = integrate.quad(lambda u: (1 - np.sin(tau * u) / (tau * u)) / u, 0, r)[0]
    lhs = Cin(tau * r)
    rhs = G3 + (1 - np.sin(tau * r) / (tau * r))
    print(f"R^3 identity at r={r}: Cin={lhs:.8f}  G_3+(1-Omega_3)={rhs:.8f}")
# R^2: Levy measure (sigma_1/|S^1|) x rho(ds), rho(ds) = b tau ds /(s sqrt(tau^2-s^2)) on (0,tau);
# its shadow on the line must be b/(2|y|) on 0<|y|<tau, i.e. profile k-bar = b.  Check via Lemma A.8 with
# k'(s) = b tau / sqrt(tau^2 - s^2) (so that rho(ds) = k'(s) ds/s).
def shadow2(r):
    U = np.sqrt(tau ** 2 / r ** 2 - 1)
    f = lambda u: b * tau / np.sqrt(tau ** 2 - r ** 2 * (1 + u * u)) / (1 + u * u)
    val, _ = integrate.quad(f, -U, U, limit=200)
    return C1 * val
for r in (0.1, 0.5, 0.9, 0.99):
    print(f"R^2: shadow profile of k'(s)=b tau/sqrt(tau^2-s^2) at r={r}: {shadow2(r):.6f} (target b={b})")
# Levy-measure integrability of rho in R^2: int (s^2 ^ 1) rho(ds) < inf
print("int (s^2 wedge 1) rho(ds) =", integrate.quad(lambda s: min(s * s, 1) * b * tau / (s * np.sqrt(tau ** 2 - s ** 2)), 0, tau)[0])
# Cin(sqrt(sigma)) is not a Bernstein function: derivative (1-cos sqrt s)/(2s) is not monotone
der = lambda s: (1 - np.cos(np.sqrt(s))) / (2 * s)
print("derivative of Cin(sqrt s) at s=pi^2, 4pi^2, 9pi^2:", der(np.pi ** 2), der(4 * np.pi ** 2), der(9 * np.pi ** 2))

print("== stages: mass of the residual's Levy measure for a datum with finite c ==")
# Matern-type profile k(r) = c e^{-r}: int_0^inf (k(r) - k(r/lam)) dr/r  should be c log(1/lam)
c, lam = 1.5, 0.4
val = integrate.quad(lambda r: c * (np.exp(-r) - np.exp(-r / lam)) / r, 0, np.inf)[0]
print("mass =", val, " c log(1/lam) =", c * np.log(1 / lam))

print("== A.19 sanity: compare with direct (3.4) integral at d=3, w=4, r=1.5 ==")
d, wv, r = 3, 4.0, 1.5
kI = lambda u: u ** -0.5 + wv * (1 <= u <= 2)
direct = 2 / special.gamma(d / 2) * integrate.quad(lambda v: v ** (d / 2 - 1) * np.exp(-v) * kI(r * r / (2 * v)), 0, np.inf, limit=400, points=[r * r / 4, r * r / 2])[0]
print("direct =", direct, " (A.19) =", k_profile(d, wv, r))
