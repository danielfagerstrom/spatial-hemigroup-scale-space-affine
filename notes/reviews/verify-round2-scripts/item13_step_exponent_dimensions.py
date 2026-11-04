r"""VERIFY round 2, item 13: the exponent of the step datum of dimension d, read in dimension D.

G_d(rho) := b int_0^tau (1 - Omega_d(r rho)) dr/r is the exponent, along a ray, of the datum
(0, b 1_(0,tau)) in dimension d (eq:polar-decomposition; Omega_d the mean of cos over the sphere).

Claims checked:
  (A) Omega_d(t) = Omega_{d+2}(t) + (t/d) Omega_{d+2}'(t), d = 1..5, hence
      G_d(rho) = G_{d+2}(rho) + (b/d) (1 - Omega_{d+2}(tau rho)):
      in dimension d+2 the Levy measure is the step datum's plus b/d times the uniform law on
      the sphere of radius tau.
  (B) dimension d+1. The profile obtained by inverting the shadow formula (the referee's Abel
      inversion), for 0 < s < tau,
          k'(s) = (b/(pi C_d)) [ (d-1) J_d(tau/s) + tau^(2-d) s^(d-1) / sqrt(tau^2 - s^2) ],
          J_d(x) = int_1^x v^(1-d) dv / sqrt(v^2 - 1),    C_d = |S^(d-1)|/|S^d|,
      which is b tau/sqrt(tau^2 - s^2) at d = 1 and (2b/pi)[arccos(s/tau) + s/sqrt(tau^2-s^2)]
      at d = 2: positive, increasing, k'(0+) = b, integrable against (s^2 ^ 1) ds/s;
      its shadow (Lemma A.8's formula) is the step b 1_(0,tau);
      its exponent int_0^tau (1 - Omega_{d+1}(s rho)) k'(s) ds/s is G_d(rho);
      and it is the shadow of the measure of (A): the shadow of the step of dimension d+2 plus
      the polar profile of the projection of the sphere.
  (C) dimension d+3 and above: no. The radial part rho_D of a rotation-invariant Levy measure on
      R^D with exponent G_d(|.|) would have the Mellin transform
          M_D(z) = b tau^z Gamma(d/2) Gamma((D+z)/2) / (z Gamma(D/2) Gamma((d+z)/2)),
      and |M_D(sigma + iy)| <= M_D(sigma) for a positive measure. The ratio is printed: bounded
      for D = d+1, d+2, unbounded for D = d+3, d+4.
  (D) a certificate that does not use (C): for a Levy exponent G on R^D with Levy measure nu,
      and a radial Schwartz h >= 0 with h(0) = 0 and Laplacian 0 at 0,
          int_{R^D} G(|zeta|) hhat(zeta) d zeta = -(2 pi)^D int h d nu <= 0.
      With h(x) = |x|^(2p) e^(-a |x|^2) the left side is computed for G = G_d: it is negative for
      D = d+1, d+2 and POSITIVE for D = d+3 (d = 1, D = 4 and d = 2, D = 5), so G_d(|.|) is not a
      Levy exponent on R^(d+3). The value is compared with the formal radial functional
      b int_0^tau h dr/r + m_1 h(tau) + m_2 tau h'(tau) read off the Mellin transform.

Run: uv run --no-project --with mpmath --with scipy python item13_step_exponent_dimensions.py
"""
from mpmath import (mp, mpf, mpc, besselj, gamma, pi, sqrt, quad, inf, exp, log, cos, sin, acos, diff,
                    hyp1f1, hyper, nstr, fabs, ci, euler, cosh, acosh)

mp.dps = 30


def Omega(n, t):
    t = mpf(t)
    if t == 0:
        return mpf(1)
    if n == 1:
        return cos(t)
    nu = mpf(n) / 2 - 1
    return gamma(mpf(n) / 2) * (2 / t) ** nu * besselj(nu, t)


def C(d):
    return gamma(mpf(d + 1) / 2) / (sqrt(pi) * gamma(mpf(d) / 2))


def G_quad(d, rho, b=1, tau=1):
    """the exponent of the step datum (0, b 1_(0,tau)) in dimension d along a ray, by quadrature"""
    rho = mpf(rho)
    if rho == 0:
        return mpf(0)
    X = tau * rho
    if d == 1:                       # b Cin(tau rho) = b (gamma_E + log X - Ci(X))
        return b * (euler + log(X) - ci(X))
    pts = [0] + [mpf(j) * 5 for j in range(1, int(X / 5) + 1)] + [X]
    return b * quad(lambda v: (1 - Omega(d, v)) / v, sorted(set(pts)))


def G(d, rho, b=1, tau=1):
    """the same, by the series of 1 - Omega_d integrated term by term:
    int_0^X (1 - Omega_d(v)) dv/v = X^2/(4d) 2F3(1, 1; 2, 2, d/2 + 1; -X^2/4)"""
    X = tau * mpf(rho)
    return b * X * X / (4 * d) * hyper([1, 1], [2, 2, mpf(d) / 2 + 1], -X * X / 4)


for _d in (1, 2, 3, 4, 5):
    for _r in (mpf("0.3"), mpf(4), mpf(37)):
        assert fabs(G(_d, _r) - G_quad(_d, _r)) < mpf(10) ** (-15), (_d, _r)

print("(A) Omega_d = Omega_{d+2} + (t/d) Omega_{d+2}', and G_d = G_{d+2} + (b/d)(1 - Omega_{d+2}(tau rho))")
for d in range(1, 6):
    for t in (mpf("0.7"), mpf("3.3"), mpf(11)):
        lhs = Omega(d, t)
        rhs = Omega(d + 2, t) + t / d * diff(lambda x: Omega(d + 2, x), t)
        assert fabs(lhs - rhs) < mpf(10) ** (-18), (d, t, lhs, rhs)
    b, tau = mpf("0.8"), mpf("1.7")
    for rho in (mpf("0.4"), mpf(2), mpf(9)):
        lhs = G(d, rho, b, tau)
        rhs = G(d + 2, rho, b, tau) + b / d * (1 - Omega(d + 2, tau * rho))
        print(f"  d = {d}, rho = {nstr(rho, 3)}: G_d = {nstr(lhs, 16)}   G_(d+2) + (b/d)(1 - Omega_(d+2)) = {nstr(rhs, 16)}")
        assert fabs(lhs - rhs) < mpf(10) ** (-14)


def J(d, x):
    """J_d(x) = int_1^x v^(1-d) dv / sqrt(v^2 - 1) = int_0^arccosh(x) cosh(u)^(1-d) du"""
    return quad(lambda u: cosh(u) ** (1 - d), [0, acosh(x)])


def kprime(d, s, b=1, tau=1):
    """the polar profile in dimension d+1 whose shadow in dimension d is the step"""
    s = mpf(s)
    if s >= tau:
        return mpf(0)
    return b / (pi * C(d)) * ((d - 1) * J(d, tau / s) + tau ** (2 - d) * s ** (d - 1) / sqrt(tau * tau - s * s))


print("(B) dimension d+1: the profile k', closed forms, positivity, monotonicity, integrability")
for s in (mpf("0.1"), mpf("0.5"), mpf("0.9"), mpf("0.999")):
    c1 = 1 / sqrt(1 - s * s)
    c2 = 2 / pi * (acos(s) + s / sqrt(1 - s * s))
    print(f"  s = {nstr(s, 4)}: d = 1: {nstr(kprime(1, s), 14)} = tau/sqrt(tau^2 - s^2) = {nstr(c1, 14)};"
          f"  d = 2: {nstr(kprime(2, s), 14)} = (2/pi)[arccos s + s/sqrt(1 - s^2)] = {nstr(c2, 14)}")
    assert fabs(kprime(1, s) - c1) < mpf(10) ** (-18) and fabs(kprime(2, s) - c2) < mpf(10) ** (-18)
for d in (1, 2, 3, 4, 5):
    vals = [kprime(d, mpf(j) / 200) for j in range(1, 200)]
    assert all(v > 0 for v in vals) and all(vals[i] <= vals[i + 1] for i in range(len(vals) - 1))
    k0 = kprime(d, mpf(10) ** (-8))
    # Levy integrability: int_0^tau k'(s) s ds (the profile vanishes beyond tau = 1)
    I1 = quad(lambda s: kprime(d, s) * s, [0, mpf("0.5"), mpf("0.9"), mpf("0.99"), mpf("0.9999"), 1])
    print(f"  d = {d}: k' > 0 and nondecreasing on (0, tau); k'(0+) = {nstr(k0, 10)} (b = 1);"
          f" int_0^tau k'(s) s ds = {nstr(I1, 10)} < infinity")
    assert fabs(k0 - 1) < mpf(10) ** (-6)


def shadow_of_kprime(d, r, b=1, tau=1):
    """Lemma A.8's formula, kbar(r) = 2 C_d r^d int_r^tau k'(s) s^(-d) ds / sqrt(s^2 - r^2),
    with s = r cosh(x) to remove the endpoint singularity at s = r, and s = tau sin(theta) near tau"""
    r = mpf(r)
    # substitution s^2 = r^2 + (tau^2 - r^2) sin^2(th): both endpoint singularities become smooth
    def integrand(th):
        s2 = r * r + (tau * tau - r * r) * sin(th) ** 2
        s = sqrt(s2)
        # ds / sqrt(s^2 - r^2) = sqrt(tau^2 - r^2) cos(th) dth / s
        # k'(s) has the factor 1/sqrt(tau^2 - s^2) = 1/(sqrt(tau^2 - r^2) cos(th))
        root = sqrt(tau * tau - r * r) * cos(th)       # sqrt(tau^2 - s^2)
        kp = b / (pi * C(d)) * ((d - 1) * J(d, tau / s) + tau ** (2 - d) * s ** (d - 1) / root)
        return kp * s ** (-d) * root / s
    return 2 * C(d) * r ** d * quad(integrand, [0, pi / 4, pi / 2])


print("    the shadow of k' in dimension d (Lemma A.8's formula) against the step b = 1 on (0, tau = 1)")
for d in (1, 2, 3, 4):
    row = []
    for r in (mpf("0.05"), mpf("0.3"), mpf("0.7"), mpf("0.97")):
        v = shadow_of_kprime(d, r)
        row.append(nstr(v, 13))
        assert fabs(v - 1) < mpf(10) ** (-10), (d, r, v)
    print(f"  d = {d}: shadow at r = 0.05, 0.3, 0.7, 0.97: {row}")

print("    the exponent of k' in dimension d+1 against G_d")
for d in (1, 2, 3):
    for rho in (mpf("0.5"), mpf(3), mpf(12)):
        def integrand(th):
            s = sin(th)
            root = cos(th)
            kp = 1 / (pi * C(d)) * ((d - 1) * J(d, 1 / s) + s ** (d - 1) / root)
            return (1 - Omega(d + 1, s * rho)) * kp / s * root
        val = quad(integrand, [0, pi / 8, pi / 4, 3 * pi / 8, pi / 2])
        ref = G(d, rho)
        print(f"  d = {d}, rho = {nstr(rho, 3)}: int (1 - Omega_(d+1)(s rho)) k'(s) ds/s = {nstr(val, 14)}   G_d = {nstr(ref, 14)}")
        assert fabs(val - ref) < mpf(10) ** (-9)

print("    k' as the shadow of the measure of (A): shadow of the step of dimension d+2, plus the sphere")
for d in (1, 2, 3):
    n = d + 1                                   # the dimension in which k' lives
    for s in (mpf("0.2"), mpf("0.6"), mpf("0.95")):
        # shadow in dimension n = d+1 of the step profile 1_(0,1) of dimension n+1 = d+2
        # direct: int_s^1 u^(-n) du / sqrt(u^2 - s^2), with u = s cosh x
        step_sh = 2 * C(n) * s ** n * quad(lambda u: u ** (-n) / sqrt(u * u - s * s), [s, (s + 1) / 2, 1])
        # the projection on R^n of the uniform law on the unit sphere of R^(n+1) has the density
        # Gamma((n+1)/2) pi^(-(n+1)/2) (1 - |x|^2)^(-1/2) on the unit ball; its polar profile is
        # |S^(n-1)| s^n times that; the rate is b/d
        sph = (2 * pi ** (mpf(n) / 2) / gamma(mpf(n) / 2)) * s ** n * gamma(mpf(n + 1) / 2) * pi ** (-mpf(n + 1) / 2) / sqrt(1 - s * s) / d
        tot = step_sh + sph
        print(f"  d = {d}, s = {nstr(s, 3)}: shadow of step {nstr(step_sh, 12)} + sphere {nstr(sph, 12)} = {nstr(tot, 13)}   k' = {nstr(kprime(d, s), 13)}")
        assert fabs(tot - kprime(d, s)) < mpf(10) ** (-9)


def Mellin(d, D, z, b=1, tau=1):
    return b * tau ** z * gamma(mpf(d) / 2) * gamma((D + z) / 2) / (z * gamma(mpf(D) / 2) * gamma((d + z) / 2))


print("(C) |M_D(sigma + i y)| / M_D(sigma), sigma = 1: at most 1 for a positive measure")
for d in (1, 2, 3):
    for D in (d + 1, d + 2, d + 3, d + 4):
        row = [nstr(fabs(Mellin(d, D, mpc(1, y))) / Mellin(d, D, mpf(1)), 6) for y in (1, 10, 100, 1000, 10000)]
        sup = max(fabs(Mellin(d, D, mpc(1, mpf(y) / 4))) / Mellin(d, D, mpf(1)) for y in range(0, 40001, 7))
        verdict = "bounded by 1" if sup <= 1 + mpf(10) ** (-20) else "EXCEEDS 1: no positive measure"
        print(f"  d = {d}, D = {D}: y = 1, 10, 100, 1000, 10000: {row}   sup on [0, 10^4]: {nstr(sup, 6)}  ({verdict})")
        assert (sup <= 1 + mpf(10) ** (-20)) == (D <= d + 2)
    # the exact Mellin transforms in dimensions d+1 (the profile k') and d+2 (step plus sphere)
    z = mpc("0.7", "2.3")
    m1 = quad(lambda th: sin(th) ** z * (1 / (pi * C(d))) * ((d - 1) * J(d, 1 / sin(th)) + sin(th) ** (d - 1) / cos(th)) / sin(th) * cos(th),
              [0, pi / 8, pi / 4, 3 * pi / 8, pi / 2])
    m2 = 1 / z + mpf(1) / d
    print(f"    d = {d}: int_0^1 s^z k'(s) ds/s = {nstr(m1, 12)}   M_(d+1)(z) = {nstr(Mellin(d, d + 1, z), 12)};"
          f"  1/z + 1/d = {nstr(m2, 12)}   M_(d+2)(z) = {nstr(Mellin(d, d + 2, z), 12)}")
    assert fabs(m1 - Mellin(d, d + 1, z)) < mpf(10) ** (-10) and fabs(m2 - Mellin(d, d + 2, z)) < mpf(10) ** (-20)


def hhat(D, p, a, rho):
    """Fourier transform int h(x) e^{i<zeta,x>} dx of h(x) = |x|^(2p) e^{-a|x|^2} on R^D, |zeta| = rho"""
    return pi ** (mpf(D) / 2) * a ** (-(p + mpf(D) / 2)) * gamma(p + mpf(D) / 2) / gamma(mpf(D) / 2) \
        * exp(-rho * rho / (4 * a)) * hyp1f1(-p, mpf(D) / 2, rho * rho / (4 * a))


def pairing(d, D, p, a):
    """int_{R^D} G_d(|zeta|) hhat(zeta) d zeta, with h scaled by e^{a} (so that h(tau = 1) = 1)"""
    area = 2 * pi ** (mpf(D) / 2) / gamma(mpf(D) / 2)
    top = 12 * sqrt(a) + 40
    pts = [mpf(j) for j in range(0, int(top) + 1, 2)]
    return area * exp(a) * quad(lambda r: G(d, r) * hhat(D, p, a, r) * r ** (D - 1), pts)


def formal(d, D, p, a):
    """the radial functional of the measure (or distribution) with Mellin transform M_D, on
    h(r) = r^(2p) e^{-a(r^2 - 1)}:  M_D(z) = sum of 1/z, constants and powers of z, i.e.
    int_0^1 h dr/r, h(1), h'(1), ...; computed from the Mellin transform of h along Re z = 1/2"""
    # int h d rho_D = (1/2 pi) int M_D(1/2 + iy) Hm(-(1/2 + iy)) dy with Hm(w) = int_0^inf h(r) r^(w-1) dr
    def Hm(w):
        return exp(a) * gamma(p + w / 2) / (2 * a ** (p + w / 2))
    f = lambda y: (Mellin(d, D, mpc("0.5", y)) * Hm(-mpc("0.5", y))).real
    return quad(f, [-inf, -40, -10, 0, 10, 40, inf]) / (2 * pi)


print("(D) the certificate: int G_d hhat over R^D, h = |x|^(2p) e^(-a(|x|^2 - 1)); a Levy exponent needs <= 0")
for d, p, a in ((1, 30, 40), (2, 30, 40)):
    for D in (d + 1, d + 2, d + 3):
        val = pairing(d, D, p, a)
        fm = formal(d, D, p, a)
        ref = -(2 * pi) ** D * fm
        sign = "<= 0, as a Levy exponent requires" if val <= 0 else "> 0: NOT a Levy exponent on R^D"
        print(f"  d = {d}, D = {D}, p = {p}, a = {a}: int G_d hhat = {nstr(val, 12)}  ({sign});"
              f"  -(2 pi)^D x (radial functional {nstr(fm, 10)}) = {nstr(ref, 12)}")
        assert fabs(val - ref) < mpf(10) ** (-8) * fabs(ref)
        if D <= d + 2:
            assert val <= 0
        if d == 1 and D == 4:
            assert val > 0
print("    (at d = 2, D = 5 this h is not a certificate: the functional is positive on it; block (E) has one)")

print("(E) the same pairing in double precision for a narrower h, p = 361, a = 400 (peak at r = 0.95)")
import numpy as np
from scipy import integrate as sint, special as ssp


def Omega_np(n, v):
    v = np.asarray(v, dtype=float)
    out = np.ones_like(v)
    nz = v > 0
    if n == 1:
        out[nz] = np.cos(v[nz])
    else:
        nu = n / 2 - 1
        out[nz] = ssp.gamma(n / 2) * (2 / v[nz]) ** nu * ssp.jv(nu, v[nz])
    return out


def pairing_np(d, D, p, a, top=520.0, step=0.002):
    rho = np.arange(0.0, top + step / 2, step)
    integrand = np.zeros_like(rho)
    integrand[1:] = (1 - Omega_np(d, rho[1:])) / rho[1:]
    Gd = np.concatenate([[0.0], sint.cumulative_simpson(integrand, x=rho)])
    x = rho * rho / (4 * a)
    logc = a + D / 2 * np.log(np.pi) - (p + D / 2) * np.log(a) + ssp.gammaln(p + 1)
    hh = np.exp(logc - x) * ssp.eval_genlaguerre(p, D / 2 - 1, x)
    area = 2 * np.pi ** (D / 2) / ssp.gamma(D / 2)
    return area * sint.simpson(Gd * hh * rho ** (D - 1), x=rho)


def formal_np(d, D, p, a):
    Y = 14 * np.sqrt(p)
    y = np.linspace(-Y, Y, 400001)
    z = 0.5 + 1j * y
    logM = ssp.loggamma(d / 2) + ssp.loggamma((D + z) / 2) - np.log(z) - ssp.loggamma(D / 2) - ssp.loggamma((d + z) / 2)
    f = np.exp(logM + a + ssp.loggamma(p - z / 2) - (p - z / 2) * np.log(a)) / 2
    return sint.simpson(f.real, x=y) / (2 * np.pi)


# the double-precision routine against the mpmath one, on the first test function
v0, r0 = pairing_np(1, 4, 30, 40, top=160.0), float(pairing(1, 4, 30, 40))
print(f"  check of the routine: d = 1, D = 4, p = 30, a = 40: {v0:.9g} (double) against {r0:.9g} (mpmath)")
assert abs(v0 - r0) < 1e-6 * abs(r0)
for d in (1, 2, 3):
    for D in (d + 1, d + 2, d + 3):
        val = pairing_np(d, D, 361, 400)
        fm = formal_np(d, D, 361, 400)
        ref = -(2 * np.pi) ** D * fm
        sign = "<= 0" if val <= 0 else "> 0: NOT a Levy exponent on R^D"
        print(f"  d = {d}, D = {D}: int G_d hhat = {val:.8g}  ({sign});  -(2 pi)^D x (radial functional {fm:.7g}) = {ref:.8g}")
        assert abs(val - ref) < 1e-5 * abs(ref)
        assert (val <= 0) == (D <= d + 2)
print("all assertions passed")
