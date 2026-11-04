"""Q-0425: numerical checks of the statements of the new blueprint nodes that the scripts of the
verification round do not already cover. Each block names the node and the clause it checks.

  1. prop:isotropic-exponent-profile(3): the two-sided bound
         c (lambda_d - 3) <= F_d(rho e) - (c log rho - log K(1/rho) + C_k) <= 13 c / 4
     at rho >= 1 (the verification record states it and checks the limit only), and the limit
     c varkappa_d, for the step profile and the Matern profile, d = 1, 2, 3, 5.
  2. prop:radial-dictionary, Step C: H_d(s) <= log^+ s + 13/4, and H_d(s)/log s -> 1.
  3. prop:radial-dictionary(1), (2) on the Matern exponent gamma log(1 + r^2/2): phi(r) =
     1 - r F'(r)/c = (1 + r^2/2)^(-1), and k_d(r) = c Pr(|X| > r) for X = sqrt(W) Z, W exponential
     of mean 1 (so that E exp(i<xi, X>) = (1 + |xi|^2/2)^(-1)), against eq:polar-profile-d.
  4. lem:shadow-polar-profile: the shadow on the line of the step of the plane is
     (2b/pi) arccos(r/tau).
  5. prop:origin-rate-profile-d(3): L(s)/log(1/s) -> K(0+), with log(1/s) <= L(s) <= K(s) log(1/s),
     on the power profile c (1 - sqrt r) 1_(0,1), whose K is closed form (the statement is one
     about K alone; the Matern case of the constant B K(0+) is c_critical_case.py).
  6. prop:separating-family-mixtures: eq:gaussian-inverse-square; E exp(-sigma 2 pi / Z_0^2) =
     exp(-2 sqrt(pi sigma)); the closed form of F_I^(w) against the definition; and
     r (F^(w))'(r) = sqrt(2 pi) r + 2w (exp(-r^2/2) - exp(-r^2)).
  7. lem:exponent-profile-constant(3), (4): the values of varkappa_d and the three closed forms.

Run: uv run --no-project --with mpmath python -u d_q0425_new_nodes.py   (about a minute)
"""
from mpmath import (mp, mpf, besselj, besselk, gamma, digamma, euler, pi, sqrt, log, exp, quad,
                    inf, acos, cos, diff, linspace)

mp.dps = 15
OK = True


def check(name, cond):
    global OK
    OK = OK and bool(cond)
    print(("  ok   " if cond else "  FAIL ") + name)


def Omega(d, t):
    """The characteristic function of the uniform law on the unit sphere of R^d at radius t."""
    t = mpf(t)
    if t == 0:
        return mpf(1)
    if d == 1:
        return cos(t)
    nu = mpf(d) / 2 - 1
    return gamma(mpf(d) / 2) * (2 / t) ** nu * besselj(nu, t)


def H(d, s):
    """H_d(s) = int_0^s (1 - Omega_d(v)) dv/v, the exponent of the step datum (0, 1_(0,1))."""
    s = mpf(s)
    pts = [0, min(s, 1)] + [x for x in range(4, int(s) + 1, 4)] + [s]
    pts = sorted(set(pts))
    return quad(lambda v: (1 - Omega(d, v)) / v, pts)


def lam(d):
    return (digamma(mpf(1) / 2) - digamma(mpf(d) / 2)) / 2


def kap(d):
    return euler + lam(d)


print("1. prop:isotropic-exponent-profile(3): the two-sided bound and the limit")
print("   (a) the step profile k_d = 1_(0,1): c = 1, K = 1, C_k = 0, Delta(rho) = H_d(rho) - log rho")
for d in (1, 2, 3, 5):
    lo, hi = lam(d) - 3, mpf(13) / 4
    row = []
    for rho in (1, 2, 5, 20, 100):
        D = H(d, rho) - log(rho)
        row.append(D)
        check(f"d={d} rho={rho}: {mp.nstr(lo, 6)} <= {mp.nstr(D, 10)} <= 3.25", lo <= D <= hi)
    check(f"d={d}: Delta(100) = {mp.nstr(row[-1], 8)} is within 0.02 of varkappa_d = "
          f"{mp.nstr(kap(d), 8)}", abs(row[-1] - kap(d)) < mpf("0.02"))

print("   (b) the Matern profile of index g: F = g log(1 + rho^2/2), c = 2g")
for d, g in ((1, mpf("0.3")), (2, mpf("0.75")), (3, mpf("1.25")), (2, mpf(2))):
    c = 2 * g
    kd = lambda r, d=d, g=g: 4 * g / gamma(mpf(d) / 2) * (r / sqrt(2)) ** (mpf(d) / 2) \
        * besselk(mpf(d) / 2, sqrt(2) * r)
    Ck = quad(lambda r: kd(r) / r, [1, 5, 20, inf])
    logK = lambda x: quad(lambda u: (c - kd(u)) / u, [x, 1])
    lo, hi = c * (lam(d) - 3), c * mpf(13) / 4
    for rho in (1, 3, 30, 1000):
        D = g * log(1 + mpf(rho) ** 2 / 2) - (c * log(rho) - logK(mpf(1) / rho) + Ck)
        check(f"d={d} g={g} rho={rho}: {mp.nstr(lo, 6)} <= {mp.nstr(D, 10)} <= {mp.nstr(hi, 6)}",
              lo <= D <= hi)
    check(f"d={d} g={g}: Delta(1000) = {mp.nstr(D, 8)} is within 2e-3 of c varkappa_d = "
          f"{mp.nstr(c * kap(d), 8)}", abs(D - c * kap(d)) < mpf("2e-3"))

print("2. prop:radial-dictionary, Step C: the two bounds on H_d")
for d in (1, 2, 3, 4):
    for s in (mpf("0.3"), 1, 7, 60):
        h = H(d, s)
        check(f"d={d} s={s}: H_d = {mp.nstr(h, 8)} <= log^+ s + 13/4",
              h <= max(log(s), 0) + mpf(13) / 4)
    check(f"d={d}: H_d(60)/log 60 = {mp.nstr(H(d, 60) / log(60), 6)} >= 1/2",
          H(d, 60) / log(60) >= mpf(1) / 2)

print("3. prop:radial-dictionary on the Matern exponent: phi and the tail of the jump size")
g = mpf("0.75")
c = 2 * g
F = lambda r: g * log(1 + r ** 2 / 2)
for r in (mpf("0.4"), 2, 9):
    phi = 1 - r * diff(F, r) / c
    check(f"r={r}: 1 - r F'(r)/c = {mp.nstr(phi, 12)} = (1 + r^2/2)^(-1)",
          abs(phi - 1 / (1 + mpf(r) ** 2 / 2)) < mpf("1e-10"))
for d in (1, 2, 3):
    # X = sqrt(W) Z, W exponential of mean 1: Pr(|X| > r) = E Pr(chi_d^2 > r^2/W)
    from mpmath import gammainc
    tail = lambda r, d=d: quad(lambda w: exp(-w) * gammainc(mpf(d) / 2, r ** 2 / (2 * w),
                                                           regularized=True), [0, 1, 10, inf])
    kd = lambda r, d=d: 4 * g / gamma(mpf(d) / 2) * (r / sqrt(2)) ** (mpf(d) / 2) \
        * besselk(mpf(d) / 2, sqrt(2) * r)
    for r in (mpf("0.5"), 2):
        check(f"d={d} r={r}: c Pr(|X| > r) = {mp.nstr(c * tail(r), 12)} = k_d(r) = "
              f"{mp.nstr(kd(r), 12)}", abs(c * tail(r) - kd(r)) < mpf("1e-9"))

print("4. lem:shadow-polar-profile at d = 1: the shadow of the step b 1_(0,tau) of the plane")
b, tau = mpf(3), mpf(2)
for r in (mpf("0.2"), 1, mpf("1.9")):
    U = sqrt(tau ** 2 / r ** 2 - 1)
    kbar = (1 / pi) * quad(lambda u: b / (1 + u ** 2), [-U, U])
    check(f"r={r}: kbar = {mp.nstr(kbar, 12)} = (2b/pi) arccos(r/tau)",
          abs(kbar - 2 * b / pi * acos(r / tau)) < mpf("1e-10"))

print("5. prop:origin-rate-profile-d(3): L(s)/log(1/s) -> K(0+), with the two bounds, on the")
print("   power profile k = c (1 - sqrt r) 1_(0,1), for which K(x) = exp(2c (1 - sqrt x))")
c = mpf("1.5")
Kf = lambda x: exp(2 * c * (1 - sqrt(x)))
K0 = exp(2 * c)
check("K by quadrature equals the closed form at x = 0.01",
      abs(exp(quad(lambda u: (c - c * (1 - sqrt(u))) / u, [mpf("0.01"), 1])) - Kf(mpf("0.01")))
      < mpf("1e-10"))
for s in (mpf("1e-2"), mpf("1e-8"), mpf("1e-60")):
    # L(s) = int_s^1 K(y) dy/y, in the variable t = log(1/y)
    L = quad(lambda tt: Kf(exp(-tt)), linspace(0, log(1 / s), 12))
    q = L / log(1 / s)
    check(f"s={mp.nstr(s, 3)}: 1 <= L/log(1/s) = {mp.nstr(q, 8)} <= K(s) = {mp.nstr(Kf(s), 8)}"
          f" <= K(0+) = {mp.nstr(K0, 8)}", 1 <= q <= Kf(s) <= K0)
check("L/log(1/s) at s = 1e-60 is within 5% of K(0+)", abs(q / K0 - 1) < mpf("0.05"))

print("6. prop:separating-family-mixtures")
for beta in (0, mpf("0.3"), 2):
    v = quad(lambda x: exp(-x ** 2 - mpf(beta) ** 2 / x ** 2), [0, 1, inf])
    check(f"beta={beta}: int exp(-x^2 - beta^2/x^2) = {mp.nstr(v, 14)} = (sqrt pi/2) e^(-2 beta)",
          abs(v - sqrt(pi) / 2 * exp(-2 * mpf(beta))) < mpf("1e-11"))
for sig in (mpf("0.2"), 1, 5):
    v = 2 / sqrt(2 * pi) * quad(lambda z: exp(-z ** 2 / 2 - sig * 2 * pi / z ** 2), [0, 1, inf])
    check(f"sigma={sig}: E exp(-sigma 2pi/Z^2) = {mp.nstr(v, 14)} = exp(-2 sqrt(pi sigma))",
          abs(v - exp(-2 * sqrt(pi * sig))) < mpf("1e-11"))
w = mpf(4)
FI_def = lambda sig: quad(lambda u: (1 - exp(-sig * u)) * u ** (-mpf(3) / 2), [0, 1, inf]) \
    + w * quad(lambda u: (1 - exp(-sig * u)) / u, [1, 2])
FI_cf = lambda sig: 2 * sqrt(pi * sig) + w * quad(lambda u: (1 - exp(-sig * u)) / u, [1, 2])
for sig in (mpf("0.1"), 1, 7):
    check(f"sigma={sig}: F_I^(w) by definition {mp.nstr(FI_def(sig), 12)} = closed form "
          f"{mp.nstr(FI_cf(sig), 12)}", abs(FI_def(sig) - FI_cf(sig)) < mpf("1e-7"))
Fw = lambda r: FI_cf(r ** 2 / 2)
for r in (mpf("0.5"), 2):
    lhs = r * diff(Fw, r)
    rhs = sqrt(2 * pi) * r + 2 * w * (exp(-r ** 2 / 2) - exp(-r ** 2))
    check(f"r={r}: r F'(r) = {mp.nstr(lhs, 12)} = sqrt(2pi) r + 2w(e^(-r^2/2) - e^(-r^2))",
          abs(lhs - rhs) < mpf("1e-9"))

print("7. lem:exponent-profile-constant(3), (4)")
check("varkappa_1 = gamma_E", abs(kap(1) - euler) < mpf("1e-12"))
check("varkappa_2 = gamma_E - log 2", abs(kap(2) - (euler - log(2))) < mpf("1e-12"))
check("varkappa_3 = gamma_E - 1", abs(kap(3) - (euler - 1)) < mpf("1e-12"))
for d in range(1, 9):
    check(f"varkappa_{d+2} = varkappa_{d} - 1/{d}", abs(kap(d + 2) - kap(d) + mpf(1) / d) < mpf("1e-12"))
    check(f"varkappa_{d} = (gamma_E - psi(d/2))/2 - log 2",
          abs(kap(d) - ((euler - digamma(mpf(d) / 2)) / 2 - log(2))) < mpf("1e-12"))
C, c, d = mpf("0.37"), mpf("1.3"), 3
A = exp(-C - c * kap(d))
check("A = 2^c exp(-C - (c/2)(gamma_E - psi(d/2)))",
      abs(A - 2 ** c * exp(-C - c / 2 * (euler - digamma(mpf(d) / 2)))) < mpf("1e-12"))
R = gamma((d - c) / 2) / (2 ** c * pi ** (mpf(d) / 2) * gamma(c / 2))
check("R(d,c) A = Gamma((d-c)/2)/(pi^(d/2) Gamma(c/2)) exp(-C - (c/2)(gamma_E - psi(d/2)))",
      abs(R * A - gamma((d - c) / 2) / (pi ** (mpf(d) / 2) * gamma(c / 2))
          * exp(-C - c / 2 * (euler - digamma(mpf(d) / 2)))) < mpf("1e-12"))
S = 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)
Bc = (2 * pi) ** (-d) * S * exp(-C - d * kap(d))
check("(2pi)^(-d) |S^(d-1)| e^(-C - d varkappa_d) = 2/(pi^(d/2) Gamma(d/2)) exp(-C - (d/2)(gamma_E - psi(d/2)))",
      abs(Bc - 2 / (pi ** (mpf(d) / 2) * gamma(mpf(d) / 2))
          * exp(-C - mpf(d) / 2 * (euler - digamma(mpf(d) / 2)))) < mpf("1e-12"))

print()
print("all checks passed" if OK else "SOME CHECK FAILED")
raise SystemExit(0 if OK else 1)
