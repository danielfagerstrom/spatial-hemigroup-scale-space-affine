r"""VERIFY round 2, item 12: a stage mu_{s,t}, 0 < s < t, of a family with no Gaussian part and
finite c is a compound Poisson law, with an atom at the centre of mass (chi(s)/chi(t))^c.

Setting. Datum (0, k_d) in dimension d, c = k_d(0+) < infinity, gauge chi, L = chi(t), l = chi(s).
The stage has the transform exp[-(F(L|xi|) - F(l|xi|))], and the difference of the exponents is
the exponent of the rotation-invariant measure nu_{s,t} with polar profile

    kappa(r) = k_d(r/L) - k_d(r/l) >= 0,        total mass  m = c log(L/l).

The Matern kernel of index gamma: F(r) = gamma log(1 + r^2/2), c = 2 gamma,
k_d(r) = (4 gamma/Gamma(d/2)) (r/sqrt 2)^(d/2) K_(d/2)(sqrt 2 r), on the line 2 gamma e^(-sqrt 2 r).
Gauge chi(t) = t. Stage transform ((1 + s^2 rho^2/2)/(1 + t^2 rho^2/2))^gamma, m = 2 gamma log(t/s),
atom (s/t)^(2 gamma).

Blocks:
  (A) the mass of the stage's Levy measure, d = 1, 2, 3, against c log(L/l); also a profile with
      a slowly varying factor (the logarithmic profile of section 3.3) and a step profile;
  (B) the exponent of that measure against F(t rho) - F(s rho), d = 1, 2, 3 (Matern);
  (C) the line, gamma = 1: the stage is (s/t)^2 delta_0 + (1 - (s/t)^2) Laplace(range t/sqrt 2),
      against the inverse transform of (transform - atom); this is the cone paper's (7.2);
  (D) the line, gamma = 3/4: the absolutely continuous part by inverse transform: nonnegative,
      mass 1 - atom; the atom as the limit of the Gaussian average (Lemma A.2(1));
  (E) the same law simulated as a compound Poisson sum (N Poisson(m) jumps +-E/U, U log-uniform
      on (sqrt 2/t, sqrt 2/s), E standard exponential): P(X = 0), E cos(omega X), P(|X| <= x);
  (F) the cascade: mu_{0,t} = mu_{s,t} * mu_{0,s} at points, with the atom and the density;
  (G) the smoothing part of a Matern stage in dimension d: its transform minus the atom decays
      like rho^(-2) for every gamma, so it is integrable on R^d only for d = 1.

Run: uv run --no-project --with mpmath --with scipy python item12_stage_compound_poisson.py
"""
import numpy as np
from mpmath import (mp, mpf, besselk, besselj, gamma, pi, sqrt, quad, quadosc, inf, exp, log, cos,
                    sin, nstr)
from scipy import integrate, special

mp.dps = 25
TOL = mpf(10) ** (-9)


def k_matern(d, g):
    if d == 1:
        return lambda r: 2 * g * exp(-sqrt(2) * r)
    return lambda r: 4 * g / gamma(mpf(d) / 2) * (r / sqrt(2)) ** (mpf(d) / 2) * besselk(mpf(d) / 2, sqrt(2) * r)


def Omega(d, x):
    if d == 1:
        return cos(x)
    if d == 2:
        return besselj(0, x)
    if d == 3:
        return sin(x) / x if x != 0 else mpf(1)
    raise ValueError


print("(A) the mass of the stage's Levy measure: int_0^inf (k(r/L) - k(r/l)) dr/r against c log(L/l)")
for d in (1, 2, 3):
    for g, s, t in ((mpf(3) / 4, mpf(1), mpf(2)), (mpf(1), mpf("0.5"), mpf(3)), (mpf("2.5"), mpf(2), mpf("2.2"))):
        k = k_matern(d, g)
        m = quad(lambda r: (k(r / t) - k(r / s)) / r, [0, s, t, 10 * t, 60 * t, inf])
        ref = 2 * g * log(t / s)
        print(f"  Matern d = {d}, gamma = {nstr(g, 3)}, s = {nstr(s, 3)}, t = {nstr(t, 3)}: "
              f"mass {nstr(m, 15)}   2 gamma log(t/s) {nstr(ref, 15)}   atom {nstr(exp(-m), 12)}"
              f"   (s/t)^(2 gamma) {nstr((s / t) ** (2 * g), 12)}")
        assert abs(m - ref) < TOL


def k_logprofile(c):
    # k(u) = c (1 - 1/(2 + log(1/u))) on (0,1], continued by (c/2) e^{-(u-1)} beyond 1
    return lambda u: c * (1 - 1 / (2 + log(1 / u))) if u <= 1 else c / 2 * exp(-(u - 1))


def k_step(b, tau):
    return lambda u: b if u < tau else mpf(0)


for name, k, c in (("logarithmic profile, c = 1.3", k_logprofile(mpf("1.3")), mpf("1.3")),
                   ("step profile b = 0.8, tau = 1", k_step(mpf("0.8"), mpf(1)), mpf("0.8"))):
    s, t = mpf(1), mpf("2.5")
    # the integrand vanishes identically near 0 for the step and tends to 0 slowly for the
    # logarithmic profile; integrate from 10^-N and add the exact head by the squeeze
    for eps in (mpf(10) ** (-6), mpf(10) ** (-12), mpf(10) ** (-24)):
        body = quad(lambda r: (k(r / t) - k(r / s)) / r, [eps, mpf(10) ** (-3), s / 2, s, t, 3 * t, 40 * t, inf])
        lo, hi = k(eps / s) * log(t / s), k(eps / t) * log(t / s)
        print(f"  {name}: eps = {nstr(eps, 3)}: int_eps^inf = {nstr(body, 12)};"
              f" c log(t/s) = {nstr(c * log(t / s), 12)};"
              f" the identity int_eps^A = int_(eps/L)^(eps/l) k dv/v - tail gives"
              f" [{nstr(lo, 10)}, {nstr(hi, 10)}] for the first term")
    # exact check of the truncation identity
    eps, A = mpf(10) ** (-4), mpf(500)
    lhs = quad(lambda r: (k(r / t) - k(r / s)) / r, [eps, mpf(10) ** (-2), s / 2, s, t, 3 * t, 40 * t, A])
    rhs = quad(lambda v: k(v) / v, [eps / t, eps / s]) - quad(lambda v: k(v) / v, [A / t, A / s])
    print(f"    truncation identity at eps = 1e-4, A = 500: {nstr(lhs, 14)} = {nstr(rhs, 14)}")
    assert abs(lhs - rhs) < mpf(10) ** (-8)

print("(B) the exponent of the stage's Levy measure against F(t rho) - F(s rho), Matern")
for d in (1, 2, 3):
    g, s, t = mpf(3) / 4, mpf(1), mpf(2)
    k = k_matern(d, g)
    for rho in (mpf("0.3"), mpf(1), mpf(4)):
        val = quad(lambda r: (1 - Omega(d, rho * r)) * (k(r / t) - k(r / s)) / r,
                   [0, mpf("0.25"), 1, 2, 4, 8, 16, 32, 64, 128])
        ref = g * log((1 + t * t * rho * rho / 2) / (1 + s * s * rho * rho / 2))
        print(f"  d = {d}, rho = {nstr(rho, 3)}: {nstr(val, 14)}   {nstr(ref, 14)}")
        assert abs(val - ref) < mpf(10) ** (-8)

print("(C) the line, gamma = 1: the stage is (s/t)^2 delta_0 + (1 - (s/t)^2) Laplace(range t/sqrt 2)")
s, t = mpf(1), mpf(2)
atom = (s / t) ** 2


def phi(om, g, s, t):
    return ((1 + s * s * om * om / 2) / (1 + t * t * om * om / 2)) ** g


for x in (mpf("0.2"), mpf(1), mpf(3)):
    inv = quadosc(lambda om: (phi(om, 1, s, t) - atom) * cos(om * x), [0, inf], omega=x) / pi
    lap = (1 - atom) * exp(-sqrt(2) * x / t) / (sqrt(2) * t)
    print(f"  x = {nstr(x, 3)}: inverse transform of (transform - atom) {nstr(inv, 12)}   closed form {nstr(lap, 12)}")
    assert abs(inv - lap) < mpf(10) ** (-8)
print(f"  atom (s/t)^2 = {nstr(atom, 6)}; the cone paper's (7.2) with r = s/t:"
      f" r^2 + 2 r (1 - r) + (1 - r)^2 = {nstr((s/t)**2 + 2*(s/t)*(1 - s/t) + (1 - s/t)**2, 6)},"
      f" continuous part 2 r (1 - r) + (1 - r)^2 = {nstr(2*(s/t)*(1 - s/t) + (1 - s/t)**2, 6)} = 1 - r^2")

print("(D) the line, gamma = 3/4, s = 1, t = 2: the absolutely continuous part")
g, s, t = 0.75, 1.0, 2.0
m = 2 * g * np.log(t / s)
atom = (s / t) ** (2 * g)
phif = lambda om: ((1 + s * s * om * om / 2) / (1 + t * t * om * om / 2)) ** g


def p_ac(x):
    """density of the absolutely continuous part at x, by the inverse cosine transform"""
    x = abs(x)
    if x < 1e-12:
        v, _ = integrate.quad(lambda om: phif(om) - atom, 0, np.inf, limit=400)
        return v / np.pi
    v, _ = integrate.quad(lambda om: phif(om) - atom, 0, np.inf, weight="cos", wvar=x, limit=400)
    return v / np.pi


xs = np.concatenate([np.linspace(0, 1, 201), np.linspace(1, 40, 1561)[1:]])
ps = np.array([p_ac(x) for x in xs])
mass = 2 * integrate.trapezoid(ps, xs)
# the tail beyond 40: the density decays like e^{-sqrt 2 x / t}
print(f"  atom (s/t)^(2 gamma) = {atom:.10f}, 1 - atom = {1 - atom:.10f}")
print(f"  min of the density on [0, 40] = {ps.min():.3e} (nonnegative), p(0) = {ps[0]:.8f}")
print(f"  2 int_0^40 p = {mass:.8f}   against 1 - atom = {1 - atom:.8f}")
assert ps.min() > -1e-9 and abs(mass - (1 - atom)) < 2e-5
# the first term of the compound Poisson series is e^{-m} times the Levy density
lev = lambda x: g * (np.exp(-np.sqrt(2) * x / t) - np.exp(-np.sqrt(2) * x / s)) / x
print(f"  Levy density at 0+: gamma sqrt2 (1/s - 1/t) = {g*np.sqrt(2)*(1/s - 1/t):.8f};"
      f" e^(-m) times it = {atom*g*np.sqrt(2)*(1/s - 1/t):.8f} <= p(0) = {ps[0]:.8f}")
for tau in (1e-2, 1e-4, 1e-6):
    v, _ = integrate.quad(lambda y: phif(y / np.sqrt(tau)) * np.exp(-y * y / 2), -np.inf, np.inf, limit=400)
    print(f"  Gaussian average: (2 pi tau)^(1/2) int g_tau dmu at tau = {tau:g}: {v / np.sqrt(2 * np.pi):.8f}")
print(f"    limit as tau -> 0: the atom {atom:.8f}")

print("(E) the same law as a compound Poisson sum, simulated (2 x 10^6 draws, seed 20261013)")
rng = np.random.default_rng(20261013)
n = 2_000_000
N = rng.poisson(m, size=n)
a_, b_ = np.sqrt(2) / t, np.sqrt(2) / s
X = np.zeros(n)
for j in range(N.max()):
    alive = N > j
    cnt = int(alive.sum())
    U = a_ * (b_ / a_) ** rng.random(cnt)          # log-uniform on (a, b): density 1/(u log(b/a))
    J = rng.exponential(1.0, cnt) / U * rng.choice([-1.0, 1.0], cnt)
    X[alive] += J
p0 = float((N == 0).mean())
se0 = np.sqrt(atom * (1 - atom) / n)
print(f"  P(X = 0) = {p0:.6f}   atom {atom:.6f}   (standard error {se0:.1e})")
assert abs(p0 - atom) < 5 * se0
for om in (0.5, 1.0, 3.0, 10.0):
    est = np.cos(om * X).mean()
    se = np.cos(om * X).std() / np.sqrt(n)
    print(f"  E cos({om} X) = {est:.6f}   transform {phif(om):.6f}   (standard error {se:.1e})")
    assert abs(est - phif(om)) < 5 * se
cum = np.concatenate([[0.0], np.cumsum((ps[1:] + ps[:-1]) / 2 * np.diff(xs))])
for x in (0.25, 1.0, 3.0):
    emp = float((np.abs(X) <= x).mean())
    ref = atom + 2 * np.interp(x, xs, cum)
    se = np.sqrt(ref * (1 - ref) / n)
    print(f"  P(|X| <= {x}) = {emp:.6f}   atom + 2 int_0^x p = {ref:.6f}   (standard error {se:.1e})")
    assert abs(emp - ref) < 5 * se + 2e-5

print("    three further seeds, 4 x 10^6 draws each: deviations in standard errors (no bias of one sign)")
for seed in (1, 2, 3):
    rng2 = np.random.default_rng(seed)
    n2 = 4_000_000
    N2 = rng2.poisson(m, size=n2)
    X2 = np.zeros(n2)
    for j in range(N2.max()):
        alive = N2 > j
        cnt = int(alive.sum())
        U = a_ * (b_ / a_) ** rng2.random(cnt)
        X2[alive] += rng2.exponential(1.0, cnt) / U * rng2.choice([-1.0, 1.0], cnt)
    devs = [((N2 == 0).mean() - atom) / np.sqrt(atom * (1 - atom) / n2)]
    for om in (0.5, 1.0, 3.0, 10.0):
        c = np.cos(om * X2)
        devs.append((c.mean() - phif(om)) / (c.std() / np.sqrt(n2)))
    print(f"  seed {seed}: P(X = 0) {devs[0]:+.2f}; E cos(omega X), omega = 0.5, 1, 3, 10: "
          + ", ".join(f"{v:+.2f}" for v in devs[1:]))
    assert max(abs(v) for v in devs) < 4

print("(F) the cascade at points: p_{0,t}(x) = atom * p_{0,s}(x) + (p_{s,t} * p_{0,s})(x), gamma = 3/4")


def p0(x, scale):
    """Matern density on the line, eq:matern-density at d = 1, dilated by `scale`"""
    y = np.abs(x) / scale
    y = np.maximum(y, 1e-300)
    nu = g - 0.5
    val = 2 / (np.sqrt(2 * np.pi) * special.gamma(g)) * (y / np.sqrt(2)) ** nu * special.kv(nu, np.sqrt(2) * y)
    lim = special.gamma(nu) / (np.sqrt(2 * np.pi) * special.gamma(g)) * 2 ** 0  # y -> 0: (y/sqrt2)^nu K_nu(sqrt2 y) -> Gamma(nu)/2
    val = np.where(y < 1e-12, lim, val)
    return val / scale


grid = np.linspace(-60, 60, 240001)
h = grid[1] - grid[0]
pst = np.interp(np.abs(grid), xs, ps, right=0.0)
for x in (0.0, 0.5, 2.0):
    conv = integrate.trapezoid(pst * p0(x - grid, s), grid)
    lhs = float(p0(np.array([x]), t)[0])
    rhs = atom * float(p0(np.array([x]), s)[0]) + conv
    print(f"  x = {x}: p_(0,t) = {lhs:.6f}   atom p_(0,s) + p_(s,t) * p_(0,s) = {rhs:.6f}")
    assert abs(lhs - rhs) < 2e-4

print("(G) the smoothing part of a Matern stage: rho^2 (transform - atom) -> 2 atom gamma (1/s^2 - 1/t^2)")
for gg in (mpf(3) / 4, mpf(3), mpf(10)):
    s, t = mpf(1), mpf(2)
    at = (s / t) ** (2 * gg)
    lim = 2 * at * gg * (1 / s ** 2 - 1 / t ** 2)
    row = [nstr(rho ** 2 * (phi(rho, gg, s, t) - at), 10) for rho in (mpf(10), mpf(100), mpf(1000))]
    print(f"  gamma = {nstr(gg, 3)}: rho^2 (phi - atom) at rho = 10, 100, 1000: {row};  limit {nstr(lim, 10)}")
print("  so the transform of the smoothing part is integrable on R^d exactly for d = 1: by Lemma A.2(2)")
print("  the smoothing part of a Matern stage is unbounded at the centre for d >= 2, whatever gamma.")
print("all assertions passed")
