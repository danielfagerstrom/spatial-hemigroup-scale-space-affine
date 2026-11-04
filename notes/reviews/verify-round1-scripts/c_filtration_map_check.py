"""Blind check of the map phi -> F_phi(r) = c int_0^r (1 - phi(u)) du/u (VERIFY-round1-prior-art.md, section 4).

Notation.  Omega_d(t) is the mean of cos(t <e, eta>) over the unit sphere of R^d:
    Omega_1 = cos,  Omega_2 = J_0,  Omega_3(t) = sin t / t,
    Omega_d(t) = Gamma(d/2) (2/t)^((d-2)/2) J_((d-2)/2)(t).
An isotropic origin datum (0, k_d) in dimension d has the exponent
    F(rho) = int_0^oo (1 - Omega_d(rho r)) k_d(r) dr/r                       (Levy form, polar coordinates)
and, with varpi = -dk_d of total mass c = k_d(0+) and sigma = varpi/c,
    F(rho) = c int_0^rho (1 - phi(u)) du/u,   phi(u) = int Omega_d(u s) sigma(ds)   (the map).

Blocks.
  A  the map and its normalisation: both forms of F, for a step and for an exponential profile,
     d = 1..4; Omega_d as a sphere mean; the logarithmic moment.
  B  the negative case d = 2, phi = Omega_2 = J_0: the folded profile, the polar profile that
     dimension 3 would need (k_3 = k_1 - r k_1'), that its exponent is F_phi, and that it increases.
  C  the positive case phi = Omega_3 = sin u/u: the profiles in dimensions 1, 2, 3 (nonincreasing),
     and what dimensions 4 and 5 would need.
  D  inf Omega_d, d = 1..10, and the mixture identity Omega_(d+1) = int Omega_d(. s) beta_d(ds)
     that proves inf Omega_d < inf Omega_(d+1) for every d.
  E  the Cin ray (d = 1, phi = cos): what the plane and R^3 would need.
  F  the two-dimension step k_(d+2) = k_d - (r/d) k_d' on the Matern profiles of the paper.
  H  the paper's family F^(w) under the map: psi_w(r) = r F^(w)'(r) = sqrt(2 pi) r
     + 2w (e^(-r^2/2) - e^(-r^2)); its Levy density in R^d is nonnegative exactly when w <= w_d.

Run: uv run --no-project --with mpmath --with scipy python c_filtration_map_check.py
"""
from mpmath import (mp, mpf, pi, sqrt, cos, sin, acos, exp, log, gamma, beta, besselj, besselk,
                    besseljzero, quad, diff, inf, findroot, e1)

mp.dps = 20
TOL = mpf(10) ** (-9)


def Omega(d, t):
    t = mpf(t)
    if t == 0:
        return mpf(1)
    if d == 1:
        return cos(t)
    if d == 3:
        return sin(t) / t
    nu = mpf(d - 2) / 2
    return gamma(mpf(d) / 2) * (2 / t) ** nu * besselj(nu, t)


def one_minus_over(f, u):
    """(1 - f(u))/u, with the value 0 at u = 0 (all f here are 1 - O(u^2))."""
    if u == 0:
        return mpf(0)
    return (1 - f(u)) / u


def close(a, b, tol=TOL):
    return abs(a - b) <= tol * (1 + abs(b))


def pts(a, b, step):
    """Break points for an oscillatory integrand on [a, b]."""
    n = int((b - a) / step) + 1
    return [a + (b - a) * mpf(i) / n for i in range(n + 1)]


# ---------------------------------------------------------------------------------------------
print("A. The map and its normalisation")
print("A0. Omega_d as the sphere mean  int_-1^1 cos(t u)(1-u^2)^((d-3)/2) du / B(1/2,(d-1)/2)")
for d in (2, 3, 4, 5):
    for t in (mpf("0.7"), mpf(4), mpf(11)):
        if d == 2:
            m = quad(lambda th: cos(t * cos(th)), [0, pi]) / pi
        else:
            m = quad(lambda u: cos(t * u) * (1 - u * u) ** (mpf(d - 3) / 2), pts(-1, 1, pi / t)) \
                / beta(mpf(1) / 2, mpf(d - 1) / 2)
        assert close(m, Omega(d, t)), (d, t)
print("    agree, d = 2..5 at t = 0.7, 4, 11")

c, tau = mpf("1.7"), mpf("0.8")
print(f"A1. step profile k_d = c 1_(0,tau), c = {c}, tau = {tau}: sigma = delta_tau, phi(u) = Omega_d(tau u)")
for d in (1, 2, 3, 4):
    for rho in (mpf("0.5"), mpf(3), mpf(12)):
        levy = c * quad(lambda r: one_minus_over(lambda x: Omega(d, rho * x), r), pts(0, tau, pi / rho))
        themap = c * quad(lambda u: one_minus_over(lambda x: Omega(d, tau * x), u), pts(0, rho, pi / tau))
        assert close(levy, themap), (d, rho)
        if rho == 3:
            print(f"    d = {d}, rho = 3: Levy form {mp.nstr(levy, 14)}   map {mp.nstr(themap, 14)}")

phi_exp = {1: lambda u: 1 / (1 + u * u),
           2: lambda u: 1 / sqrt(1 + u * u),
           3: lambda u: mp.atan(u) / u if u != 0 else mpf(1),
           4: lambda u: 2 / (sqrt(1 + u * u) + 1)}  # = 2 (sqrt(1+u^2) - 1)/u^2, in the stable form
print("A2. exponential profile k_d = c e^(-r): sigma = Exp(1), phi(u) = int_0^oo Omega_d(u s) e^(-s) ds")
for d in (1, 2, 3, 4):
    u0 = mpf("2.3")
    num = quad(lambda s: Omega(d, u0 * s) * exp(-s), pts(0, 60, pi / u0))
    assert close(num, phi_exp[d](u0)), d
    for rho in (mpf("0.5"), mpf(3)):
        levy = c * quad(lambda r: one_minus_over(lambda x: Omega(d, rho * x), r) * exp(-r),
                        pts(0, 60, pi / rho))
        themap = c * quad(lambda u: one_minus_over(phi_exp[d], u), [0, rho])
        assert close(levy, themap), (d, rho)
        if rho == 3:
            print(f"    d = {d}, rho = 3: Levy form {mp.nstr(levy, 14)}   map {mp.nstr(themap, 14)}"
                  f"   phi(2.3) = {mp.nstr(num, 10)}")
lhs = quad(lambda r: exp(-r) / r, [1, 10, inf])
rhs = quad(lambda s: log(s) * exp(-s), [1, 10, inf])
print(f"A3. logarithmic moment, k = e^(-r): int_1^oo k dr/r = {mp.nstr(lhs, 14)},"
      f" int log^+ s sigma(ds) = {mp.nstr(rhs, 14)}, E_1(1) = {mp.nstr(e1(1), 14)}")
assert close(lhs, rhs) and close(lhs, e1(1))

# ---------------------------------------------------------------------------------------------
print()
print("B. Negative case: d = 2, phi = Omega_2 = J_0 (the step profile 1_(0,1) in the plane), c = 1")
J0 = lambda u: besselj(0, u)
Fphi = lambda rho: quad(lambda u: one_minus_over(J0, u), pts(0, rho, 3))
k1 = lambda x: 2 / pi * acos(x)
k3 = lambda r: 2 / pi * (acos(r) + r / sqrt(1 - r * r))
for rho in (mpf("0.5"), mpf(2), mpf(7), mpf(20)):
    F = Fphi(rho)
    G1 = quad(lambda x: one_minus_over(lambda y: cos(rho * y), x) * k1(x), pts(0, 1, pi / rho))
    # r = sin th: k_3(r) dr/r = (2/pi) ((pi/2 - th) cos th + sin th) / sin th  dth
    G3 = quad(lambda th: (1 - Omega(3, rho * sin(th))) * 2 / pi
              * ((pi / 2 - th) * cos(th) + sin(th)) / sin(th) if th != 0 else mpf(0),
              pts(0, pi / 2, pi / rho))
    print(f"    rho = {mp.nstr(rho, 3):>4}: F_phi = {mp.nstr(F, 14)}   line form with k_1 = {mp.nstr(G1, 14)}"
          f"   R^3 form with k_3 = {mp.nstr(G3, 14)}")
    assert close(F, G1) and close(F, G3)
print("    k_1(x) = (2/pi) arccos x is concave on (0,1); the shadow on a line of a nonincreasing")
print("    profile in R^3 is convex (k_1(x) = int_(s>x) (1 - x/s) varpi_3(ds)).")
print("    the polar profile dimension 3 needs, k_3(r) = k_1 - r k_1' = (2/pi)(arccos r + r/sqrt(1-r^2)):")
prev = None
for r in ("0.001", "0.1", "0.3", "0.5", "0.7", "0.9", "0.99", "0.999"):
    v = k3(mpf(r))
    dv = diff(k3, mpf(r))
    print(f"      r = {r:>5}: k_3 = {mp.nstr(v, 10):>14}   k_3' = {mp.nstr(dv, 8)}")
    assert dv > 0 and (prev is None or v > prev)
    prev = v
print("    k_3 >= 0, strictly increasing on (0,1), unbounded at 1-, and 0 beyond 1: NOT nonincreasing.")
print("    shadow in the plane of the R^3 measure with profile k_3 (formula of item09), should be 1_(0,1):")
for r in (mpf("0.2"), mpf("0.6"), mpf("0.95")):
    um = sqrt(1 / r ** 2 - 1)
    kb = quad(lambda u: k3(r * sqrt(1 + u * u)) * (1 + u * u) ** (-mpf(3) / 2), [0, um / 2, um])
    print(f"      r = {mp.nstr(r, 3)}: kbar_2 = {mp.nstr(kb, 12)}")
    assert close(kb, 1, mpf(10) ** (-7))
q = J0(besseljzero(1, 1))
print(f"    J_0 is not positive definite on R^3: a regular tetrahedron of edge j_(1,1) ="
      f" {mp.nstr(besseljzero(1, 1), 8)} gives the eigenvalue 1 + 3 J_0 = {mp.nstr(1 + 3 * q, 8)} < 0")
assert 1 + 3 * q < 0

# ---------------------------------------------------------------------------------------------
print()
print("C. Positive case: phi = Omega_3 = sin u/u (the step profile 1_(0,1) in R^3), c = 1")
sinc = lambda u: Omega(3, u)
Fpos = lambda rho: quad(lambda u: one_minus_over(sinc, u), pts(0, rho, 3))
Om5 = lambda t: Omega(5, t)  # = 3 (sin t - t cos t)/t^3, through the Bessel form (stable near 0)
for rho in (mpf("0.5"), mpf(2), mpf(7), mpf(20)):
    F = Fpos(rho)
    G3 = quad(lambda r: one_minus_over(lambda y: sinc(rho * y), r), pts(0, 1, pi / rho))
    G2 = quad(lambda r: one_minus_over(lambda y: J0(rho * y), r) * sqrt(1 - r * r), pts(0, 1, pi / rho))
    G1 = quad(lambda x: one_minus_over(lambda y: cos(rho * y), x) * (1 - x), pts(0, 1, pi / rho))
    # dimension 4 would need k_4 = k_2 - (r/2) k_2' = (2 - r^2)/(2 sqrt(1 - r^2)); r = sin th
    G4 = quad(lambda th: (1 - Omega(4, rho * sin(th))) * (2 - sin(th) ** 2) / (2 * sin(th))
              if th != 0 else mpf(0), pts(0, pi / 2, pi / rho))
    # dimension 5 would need k_5 = k_3 - (r/3) k_3' = 1_(0,1) + (1/3) delta_1 (a measure, not a function)
    G5 = quad(lambda r: one_minus_over(lambda y: Om5(rho * y), r), pts(0, 1, pi / rho)) \
        + (1 - Om5(rho)) / 3
    print(f"    rho = {mp.nstr(rho, 3):>4}: F_phi = {mp.nstr(F, 13)}; with k_3 = 1_(0,1): {mp.nstr(G3, 13)};"
          f" k_2 = sqrt(1-r^2): {mp.nstr(G2, 13)}; k_1 = (1-x)_+: {mp.nstr(G1, 13)}")
    print(f"               what R^4 needs, k_4 = (2-r^2)/(2 sqrt(1-r^2)): {mp.nstr(G4, 13)};"
          f" what R^5 needs, 1_(0,1) + delta_1/3: {mp.nstr(G5, 13)}")
    assert close(F, G3) and close(F, G2) and close(F, G1) and close(F, G4) and close(F, G5)
print("    k_1, k_2, k_3 are nonincreasing: F_phi is in A_1, A_2, A_3.")
k4 = lambda r: (2 - r * r) / (2 * sqrt(1 - r * r))
for r in ("0.1", "0.5", "0.9"):
    assert diff(k4, mpf(r)) > 0
print("    k_4 is strictly increasing on (0,1) (k_4' = r^3 (1-r^2)^(-3/2)/2 > 0): F_phi is not in A_4,")
print("    as Omega_3 is not in Phi_4.")

# ---------------------------------------------------------------------------------------------
print()
print("D. inf Omega_d = Omega_d(first positive zero of J_(d/2)), against -1/d")
infs = []
for d in range(1, 11):
    t = besseljzero(mpf(d) / 2, 1)
    v = Omega(d, t)
    # check that it is the global minimum on a grid
    g = min(Omega(d, mpf(i) / 20) for i in range(1, 1200))
    assert v <= g + mpf(10) ** (-6)
    infs.append(v)
    print(f"    d = {d:>2}: argmin = {mp.nstr(t, 8):>10}   inf Omega_d = {mp.nstr(v, 8):>12}   -1/d = {mp.nstr(-mpf(1) / d, 6)}")
assert all(infs[i] < infs[i + 1] for i in range(len(infs) - 1))
print("    strictly increasing in d on this range. For every d it follows from the identity below:")
print("    Omega_(d+1)(t) = int_0^1 Omega_d(t s) beta_d(ds), beta_d(ds) = 2 s^(d-1) (1-s^2)^(-1/2) ds / B(d/2,1/2)")
for d in (1, 2, 3, 4):
    for t in (mpf(1), mpf("3.83"), mpf(10)):
        # s = sin th: beta_d(ds) = 2 sin^(d-1) th dth / B(d/2, 1/2)
        m = quad(lambda th: Omega(d, t * sin(th)) * 2 * sin(th) ** (d - 1), pts(0, pi / 2, pi / t)) \
            / beta(mpf(d) / 2, mpf(1) / 2)
        assert close(m, Omega(d + 1, t)), (d, t)
print("    verified for d = 1..4 at t = 1, 3.83, 10.")

# ---------------------------------------------------------------------------------------------
print()
print("E. The Cin ray: d = 1, phi = cos, F = Cin (b = tau = 1)")
Cin = lambda rho: quad(lambda v: one_minus_over(cos, v), pts(0, rho, 3))
for rho in (mpf("0.5"), mpf(2), mpf(7), mpf(20)):
    F = Cin(rho)
    # the plane would need k_2(s) = 1/sqrt(1 - s^2) on (0,1); s = sin th: k_2 ds/s = dth / sin th
    G2 = quad(lambda th: (1 - J0(rho * sin(th))) / sin(th) if th != 0 else mpf(0), pts(0, pi / 2, pi / rho))
    # R^3 would need k_3 = k_1 - r k_1' = 1_(0,1) + delta_1
    G3 = quad(lambda r: one_minus_over(lambda y: sinc(rho * y), r), pts(0, 1, pi / rho)) + (1 - sinc(rho))
    print(f"    rho = {mp.nstr(rho, 3):>4}: Cin = {mp.nstr(F, 14)}   plane form with k_2 = (1-s^2)^(-1/2): {mp.nstr(G2, 14)}"
          f"   R^3 form with 1_(0,1) + delta_1: {mp.nstr(G3, 14)}")
    assert close(F, G2) and close(F, G3)
print("    so Cin(|xi|) is the exponent of an infinitely divisible law on R^2 and on R^3 (a nonnegative")
print("    Levy measure), and the profile it needs in the plane, (1-s^2)^(-1/2), increases: not in A_2.")
print(f"    cos is not in Phi_2: inf J_0 = {mp.nstr(infs[1], 8)} > -1 = cos(pi)")

# ---------------------------------------------------------------------------------------------
print()
print("F. The two-dimension step k_(d+2) = k_d - (r/d) k_d' on the Matern profiles")
print("   k_d(r) = (4 g / Gamma(d/2)) (r^2/2)^(d/4) K_(d/2)(sqrt 2 r)   (eq:polar-profile-d with k_I = g e^(-u))")
g = mpf(3) / 4


def k_matern(d):
    return lambda r: 4 * g / gamma(mpf(d) / 2) * (r * r / 2) ** (mpf(d) / 4) * besselk(mpf(d) / 2, sqrt(2) * r)


for d in (1, 2, 3, 4):
    for r in (mpf("0.05"), mpf("0.5"), mpf(2)):
        a = k_matern(d)(r) - r / d * diff(k_matern(d), r)
        b = k_matern(d + 2)(r)
        assert close(a, b, mpf(10) ** (-8)), (d, r)
print("    verified for d = 1..4 at r = 0.05, 0.5, 2.")

# ---------------------------------------------------------------------------------------------
print()
print("H. The paper's family F^(w) under the map (it has c = infinity, so phi does not exist; the")
print("   driver's exponent psi(r) = r F'(r) does)")


def FI_prime(w, s):  # d/d sigma of int (1 - e^(-sigma u)) (u^(-1/2) + w 1_[1,2](u)) du/u
    return quad(lambda u: exp(-s * u) * u ** (-mpf(1) / 2), [0, 1, inf]) + w * quad(lambda u: exp(-s * u), [1, 2])


psi = lambda w, r: sqrt(2 * pi) * r + 2 * w * (exp(-r * r / 2) - exp(-r * r))
for w in (mpf(1), mpf(4)):
    for r in (mpf("0.3"), mpf(1), mpf(3)):
        a = r * r * FI_prime(w, r * r / 2)
        assert close(a, psi(w, r)), (w, r)
print("    r F^(w)'(r) = sqrt(2 pi) r + 2w (e^(-r^2/2) - e^(-r^2)): verified at w = 1, 4, r = 0.3, 1, 3.")
print("    Levy density of psi_w on R^d:  sqrt(2 pi) Gamma(m) pi^(-m) |x|^(-d-1) + 2w (g_2(x) - g_1(x)),")
print("    g_u the centred Gaussian density of covariance u I, m = (d+1)/2.")


def w_crit(d):
    m = mpf(d + 1) / 2
    h = lambda z: z ** m * (exp(-z) - 2 ** (-mpf(d) / 2) * exp(-z / 2))
    best = max((h(mpf(i) / 200 * d * log(2)), i) for i in range(1, 200))
    z0 = findroot(lambda z: diff(h, z), best[1] * d * log(2) / 200)
    return gamma(m) / (2 * h(z0)), z0


def levy_density_scaled(d, w, x):  # |x|^(d+1) times the density
    m = mpf(d + 1) / 2
    g = lambda u: (2 * pi * u) ** (-mpf(d) / 2) * exp(-x * x / (2 * u))
    return sqrt(2 * pi) * gamma(m) * pi ** (-m) + 2 * w * x ** (d + 1) * (g(2) - g(1))


def witness_k(d, w):  # eq:witness-polar
    m = mpf(d + 1) / 2
    P = lambda s, x: mp.gammainc(s, 0, x, regularized=True)
    return lambda r: 2 ** (mpf(3) / 2) * gamma(m) / gamma(mpf(d) / 2) / r \
        + 2 * w * (P(mpf(d) / 2, r * r / 2) - P(mpf(d) / 2, r * r / 4))


ws = []
for d in range(1, 9):
    wd, z0 = w_crit(d)
    ws.append(wd)
    x0 = sqrt(2 * z0)
    lo = levy_density_scaled(d, wd * (1 - mpf("0.001")), x0)
    hi = levy_density_scaled(d, wd * (1 + mpf("0.001")), x0)
    at = levy_density_scaled(d, wd, x0)
    grid_min = min(levy_density_scaled(d, wd, mpf(i) / 50) for i in range(1, 500))
    print(f"    d = {d}: w_d = {mp.nstr(wd, 8):>10}  sqrt(d) w_d = {mp.nstr(sqrt(d) * wd, 6):>8}"
          f"  scaled density at the critical radius: w = 0.999 w_d: {mp.nstr(lo, 3)},"
          f" w = w_d: {mp.nstr(at, 3)}, w = 1.001 w_d: {mp.nstr(hi, 3)}")
    assert lo > 0 > hi and abs(at) < mpf(10) ** (-12) and grid_min > -mpf(10) ** (-12)
    # the radial measure of the driver is -dk_d: |S^(d-1)| r^(d-1) density(r) = -k_d'(r)
    for r in (mpf("0.7"), mpf("1.9")):
        S = 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)
        a = S * levy_density_scaled(d, mpf(2), r) / r ** 2
        b = -diff(witness_k(d, mpf(2)), r)
        assert close(a, b, mpf(10) ** (-8)), (d, r)
assert all(ws[i] > ws[i + 1] for i in range(len(ws) - 1))
print(f"    sqrt(pi) = {mp.nstr(sqrt(pi), 6)}")
print("    so: F^(w) is in A_d  <=>  psi_w is a Levy exponent on R^d  <=>  w <= w_d; and the radial")
print("    measure of the driver is -dk_d^(w) (checked against eq:witness-polar at w = 2).")
print()
print("all assertions passed")
