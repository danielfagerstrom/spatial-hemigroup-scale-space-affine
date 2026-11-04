"""Round-1 verification, prior art (Q-0423): numerical checks behind
records/affine/reviews/VERIFY-round1-prior-art.md.

Run:  uv run --no-project --with mpmath python b_hankel_prior_art.py

What is checked (each block prints PASS/FAIL lines and the numbers):

 A. The ball-inversion formula. For a rotation-invariant law mu on R^d with radial
    characteristic function chi(t) = mu^(t e),
        mu(B_s) = 2^(1-d/2)/Gamma(d/2) * s^((d-1)/2) * F_nu(s),
        F_nu(s) = int_0^{oo-} f(t) (st)^(1/2) J_nu(st) dt,  nu = d/2,  f(t) = t^((d-3)/2) chi(t),
    the Hankel transform of Bingham-Inoue (1.1). Checked at the Matern law
    chi(t) = (1 + t^2/2)^(-gamma) against the direct integral of the closed-form density.
 B. The constant. Bingham-Inoue's Theorem 1.2 at nu = d/2, rho = (d-3)/2 - c gives
        mu(B_s) ~ 2^(-c) Gamma((d-c)/2) / (Gamma(d/2) Gamma(1+c/2)) * chi(1/s),
    which is the paper's R(d,c) |S^(d-1)| / c, and Cygan-Grzywny-Trojan's C~_{d,alpha} at alpha = c;
    R(d,c) is their A~_{d,alpha} and Aronszajn-Smith's constant in (4,2).
 C. The boundary c = d: Theorem 1.1 with (1.4), at the Matern law d = 2, gamma = 1 (and d = 3,
    gamma = 3/2), including the second-order constant of (1.4).
 D. The hypotheses for the class: t F'(t) -> c in d >= 2 and not in d = 1 (step profile);
    f eventually decreasing iff c > (d-3)/2; a law with d = 4, c < 1/2 and one with d = 5, c < 1
    for which f increases (Theorem 1.2 does not apply) while the rate of Proposition 3.15 holds.
 E. Aronszajn-Smith: p(x) = 2^(d/2) G_{2 gamma}(sqrt2 x) is the paper's (3.7); the three regimes
    of (4,2) with their constants.
 F. The map phi -> F(r) = int_0^r (1 - phi(u)) du/u and the dimension walk: (1-t)_+ is in Phi_1
    and not in Phi_2 (its inverse Hankel transform in the plane takes negative values); the infima
    of Schoenberg's Omega_d increase strictly, so Omega_d is in Phi_d and not in Phi_(d+1).
 G. Cygan-Grzywny-Trojan's constants C~_{d,alpha} and A~_{d,alpha} are the paper's ball constant
    and R(d,alpha).
 H. Leonenko-Olenko 2013: 1/c_1(n,alpha) is the paper's ball constant and 1/c_2(n,alpha) is
    R(n,alpha) (Theorems 2-4, Remarks 1-2); their Theorem 3 at three Matern laws with
    alpha <= (n-3)/2, where the Hankel theorem does not apply; their Example 3 is the Bessel kernel.
"""
from mpmath import (mp, mpf, gamma, besselj, besselk, quad, quadosc, sqrt, pi, log, digamma,
                    euler, inf, cos, sin, linspace)

mp.dps = 25
OK = True


def check(name, cond, detail=""):
    global OK
    OK = OK and bool(cond)
    print(("PASS  " if cond else "FAIL  ") + name + ("   " + detail if detail else ""))


def sphere(d):
    return 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)


def R(d, c):
    return gamma((mpf(d) - c) / 2) / (2 ** c * pi ** (mpf(d) / 2) * gamma(mpf(c) / 2))


def chi(t, g):
    return (1 + t * t / 2) ** (-g)


def matern_q(r, d, g):
    """The paper's (3.7): the radial density of the law with transform (1+|xi|^2/2)^(-gamma)."""
    nu = g - mpf(d) / 2
    return 2 / ((2 * pi) ** (mpf(d) / 2) * gamma(g)) * (r / sqrt(2)) ** nu * besselk(nu, sqrt(2) * r)


def ball_direct(s, d, g):
    return sphere(d) * quad(lambda r: matern_q(r, d, g) * r ** (d - 1), [0, s / 4, s])


def hankel_F(s, d, g):
    """Bingham-Inoue's F_nu(s), nu = d/2, f(t) = t^((d-3)/2) chi(t), as an improper integral."""
    nu = mpf(d) / 2
    f = lambda t: t ** ((mpf(d) - 3) / 2) * chi(t, g) * sqrt(s * t) * besselj(nu, s * t)
    head = quad(f, linspace(0, 20 / s, 21))
    tail = quadosc(f, [20 / s, inf], omega=s)
    return head + tail


def ball_hankel(s, d, g):
    return 2 ** (1 - mpf(d) / 2) / gamma(mpf(d) / 2) * s ** ((mpf(d) - 1) / 2) * hankel_F(s, d, g)


def ball_const(d, c):
    return 2 ** (-c) * gamma((mpf(d) - c) / 2) / (gamma(mpf(d) / 2) * gamma(1 + mpf(c) / 2))


def BI_const(nu, rho):
    """The constant of Bingham-Inoue's Theorem 1.2."""
    return 2 ** (rho + mpf(1) / 2) * gamma(mpf(3) / 4 + nu / 2 + rho / 2) / gamma(mpf(1) / 4 + nu / 2 - rho / 2)


print("== A. ball inversion as a Hankel transform (Matern law) ==")
for d, g, s in [(2, mpf(3) / 4, mpf(1) / 2), (3, mpf(3) / 4, mpf(1) / 2), (2, mpf(1) / 4, mpf(1) / 3),
                (3, mpf(1) / 5, mpf(1) / 3), (1, mpf(1) / 4, mpf(1) / 2), (4, mpf(3) / 4, mpf(1) / 2)]:
    a, b = ball_direct(s, d, g), ball_hankel(s, d, g)
    check(f"d={d} gamma={g} s={s}: mu(B_s) direct = Hankel", abs(a - b) < mpf(10) ** (-8),
          f"direct {mp.nstr(a, 12)}  Hankel {mp.nstr(b, 12)}")

print("\n== B. the constant of Theorem 1.2 at nu = d/2, rho = (d-3)/2 - c ==")
for d in [1, 2, 3, 4, 5, 7]:
    for c in [mpf(1) / 10, mpf(1) / 2, mpf(9) / 10, mpf(3) / 2, mpf(5) / 2, mpf(4)]:
        if not (c < d):
            continue
        nu, rho = mpf(d) / 2, (mpf(d) - 3) / 2 - c
        lhs = 2 ** (1 - mpf(d) / 2) / gamma(mpf(d) / 2) * BI_const(nu, rho)
        ok = abs(lhs / ball_const(d, c) - 1) < mpf(10) ** (-18) and \
            abs(R(d, c) * sphere(d) / c / ball_const(d, c) - 1) < mpf(10) ** (-18)
        in_range = (-nu - mpf(3) / 2 < rho < 0)
        check(f"d={d} c={c}: BI constant = paper's ball constant = R(d,c)|S|/c", ok,
              f"rho={mp.nstr(rho, 4)} in (-nu-3/2, 0): {in_range}")
print("   (the identity of the constants is algebraic and holds for every 0 < c < d; the theorem")
print("    applies only where rho < 0, i.e. c > (d-3)/2.)")

print("\n   the limit itself, mu(B_s) / (ball_const * chi(1/s)), Matern c = 2 gamma:")
for d, g in [(2, mpf(3) / 4), (3, mpf(3) / 4), (2, mpf(1) / 4), (3, mpf(1) / 5)]:
    row = []
    for s in [mpf(10) ** (-2), mpf(10) ** (-4), mpf(10) ** (-6)]:
        row.append(ball_direct(s, d, g) / (ball_const(d, 2 * g) * chi(1 / s, g)))
    check(f"d={d} gamma={g}: ratio -> 1", abs(row[-1] - 1) < mpf(1) / 50,
          "  ".join(mp.nstr(x, 8) for x in row))
print("   and for the density, q(s) / (R(d,c) s^-d chi(1/s)):")
for d, g in [(2, mpf(3) / 4), (3, mpf(3) / 4), (2, mpf(1) / 4)]:
    row = [matern_q(s, d, g) / (R(d, 2 * g) * s ** (-d) * chi(1 / s, g))
           for s in [mpf(10) ** (-2), mpf(10) ** (-4), mpf(10) ** (-6)]]
    check(f"d={d} gamma={g}: ratio -> 1", abs(row[-1] - 1) < mpf(1) / 50,
          "  ".join(mp.nstr(x, 10) for x in row))

print("\n== C. the boundary c = d: Theorem 1.1 and (1.4) ==")
for d in [2, 3]:
    g = mpf(d) / 2
    nu = mpf(d) / 2
    k0 = 1 / (2 ** nu * gamma(nu + 1))
    second = k0 * (log(2) - euler / 2 + digamma(nu + 1) / 2)
    for x in [mpf(20), mpf(200)]:
        s = 1 / x
        # Fbar(x) = x^(nu+1/2) F_nu(1/x);  mu(B_s) = 2^(1-d/2)/Gamma(d/2) s^d Fbar(1/s)
        Fbar = ball_direct(s, d, g) / (2 ** (1 - mpf(d) / 2) / gamma(mpf(d) / 2) * s ** d)
        P = quad(lambda t: t ** (d - 1) * chi(t, g), linspace(0, x, 9))  # int_0^x t^(nu+1/2) f(t) dt
        ell = x ** d * chi(x, g)  # x^(nu+3/2) f(x)
        lhs = (Fbar - k0 * P) / ell
        check(f"d={d} x={x}: (1.4), (Fbar - k0 P)/(x^(nu+3/2) f) -> k0 (log 2 - gamma_E/2 + psi(nu+1)/2)",
              abs(lhs - second) < (mpf(1) / 10 if x < 100 else mpf(1) / 100),
              f"value {mp.nstr(lhs, 8)}  limit {mp.nstr(second, 8)}")
    # leading order against the paper's boundary form: mu(B_s) ~ (2 pi)^-d V_d s^d I(s)
    s = mpf(10) ** (-4)
    Vd = pi ** (mpf(d) / 2) / gamma(mpf(d) / 2 + 1)
    I = sphere(d) * quad(lambda t: t ** (d - 1) * chi(t, g), linspace(0, 1 / s, 13))
    r1 = ball_direct(s, d, g) / ((2 * pi) ** (-d) * Vd * s ** d * I)
    r2 = (2 ** (1 - d) / (gamma(mpf(d) / 2) * gamma(mpf(d) / 2 + 1))) / ((2 * pi) ** (-d) * Vd * sphere(d))
    check(f"d={d}: Theorem 1.1's leading constant 2^(1-d)/(Gamma(d/2)Gamma(d/2+1)) = (2pi)^-d V_d |S|",
          abs(r2 - 1) < mpf(10) ** (-18), f"ball ratio at s=1e-4: {mp.nstr(r1, 8)} (slow, logarithmic)")

print("\n== D. the hypotheses for the class ==")


def Omega(d, u):
    """The mean of exp(i u <e, theta>) over the unit sphere of R^d."""
    if d == 1:
        return cos(u)
    lam = mpf(d) / 2 - 1
    return gamma(mpf(d) / 2) * (2 / u) ** lam * besselj(lam, u)


# step profile k_d = c 1_(0,1):  t F'(t) = c (1 - Omega_d(t))  (layer cake, varpi = c delta_1)
for d in [1, 2, 3, 4]:
    vals = [1 - Omega(d, mpf(t)) for t in [50, 51, 52, 53, 500, 501, 502, 503]]
    spread = max(vals) - min(vals)
    if d == 1:
        check("d=1, step profile: t F'(t)/c = 1 - cos t does not converge", spread > 1,
              "values " + " ".join(mp.nstr(v, 4) for v in vals))
    else:
        check(f"d={d}, step profile: t F'(t)/c = 1 - Omega_d(t) -> 1", abs(vals[-1] - 1) < mpf(1) / 10,
              "values " + " ".join(mp.nstr(v, 4) for v in vals))
# the layer-cake identity itself, d = 2, step profile: F(t) = c int_0^1 (1 - J_0(t r)) dr/r
c = mpf(1)
F2 = lambda t: c * quad(lambda r: (1 - besselj(0, t * r)) / r, linspace(0, 1, 30))
t0, h = mpf(7), mpf(10) ** (-6)
num = t0 * (F2(t0 + h) - F2(t0 - h)) / (2 * h)
check("d=2: t F'(t) = c (1 - J_0(t)) (numerical derivative at t = 7)",
      abs(num - c * (1 - besselj(0, t0))) < mpf(10) ** (-8), f"{mp.nstr(num, 12)} vs {mp.nstr(c*(1-besselj(0,t0)), 12)}")

# f(t) = t^((d-3)/2) chi(t), Matern: t f'/f = (d-3)/2 - 2 gamma t^2/(2+t^2) -> (d-3)/2 - c
for d, g in [(4, mpf(3) / 20), (5, mpf(2) / 5), (4, mpf(3) / 4), (5, mpf(3) / 4)]:
    cc = 2 * g
    slope = lambda t: (mpf(d) - 3) / 2 - 2 * g * t * t / (2 + t * t)
    lim = (mpf(d) - 3) / 2 - cc
    dec = slope(mpf(10) ** 6) < 0
    check(f"d={d} c={cc}: f eventually decreasing iff c > (d-3)/2", dec == (cc > (mpf(d) - 3) / 2),
          f"t f'/f -> {mp.nstr(lim, 4)}; decreasing: {dec}")
    row = [matern_q(s, d, g) / (R(d, cc) * s ** (-d) * chi(1 / s, g))
           for s in [mpf(10) ** (-2), mpf(10) ** (-4), mpf(10) ** (-6)]]
    check(f"d={d} c={cc}: the rate of Prop. 3.15 holds all the same (closed form)", abs(row[-1] - 1) < mpf(1) / 50,
          "  ".join(mp.nstr(x, 10) for x in row))

print("\n== E. Aronszajn-Smith (4,1), (4,2), (4,6) against the paper's (3.7) ==")


def G(alpha, r, n):
    return besselk((mpf(n) - alpha) / 2, r) * r ** ((alpha - n) / 2) / (
        2 ** ((mpf(n) + alpha - 2) / 2) * pi ** (mpf(n) / 2) * gamma(alpha / 2))


for d, g in [(1, mpf(3) / 4), (2, mpf(3) / 4), (3, mpf(3) / 4), (2, mpf(1)), (3, mpf(2)), (4, mpf(1) / 3)]:
    r = mpf(37) / 100
    a, b = matern_q(r, d, g), 2 ** (mpf(d) / 2) * G(2 * g, sqrt(2) * r, d)
    check(f"d={d} gamma={g}: p(x) = 2^(d/2) G_(2 gamma)(sqrt2 x)", abs(a / b - 1) < mpf(10) ** (-18))
for d, g in [(2, mpf(3) / 4), (3, mpf(3) / 4)]:
    r = mpf(10) ** (-8)
    lead = gamma(mpf(d) / 2 - g) / (2 ** g * pi ** (mpf(d) / 2) * gamma(g)) * r ** (2 * g - d)
    as_const = 2 ** (mpf(d) / 2) * R(d, 2 * g) * (sqrt(2) * r) ** (2 * g - d)  # (4,2), alpha < n, rescaled
    check(f"d={d} gamma={g}: power regime, (4,2) rescaled = paper's constant",
          abs(as_const / lead - 1) < mpf(10) ** (-18) and abs(matern_q(r, d, g) / lead - 1) < mpf(10) ** (-3))
for d in [2, 3]:
    g = mpf(d) / 2
    r = mpf(10) ** (-12)
    paper = 2 * (2 * pi) ** (-mpf(d) / 2) / gamma(mpf(d) / 2)
    as_c = 2 ** (mpf(d) / 2) / (2 ** (d - 1) * pi ** (mpf(d) / 2) * gamma(mpf(d) / 2))
    check(f"d={d}: logarithmic regime, (4,2) rescaled = 2 (2pi)^(-d/2)/Gamma(d/2)",
          abs(as_c / paper - 1) < mpf(10) ** (-18),
          f"p(r)/(const log(1/r)) at r=1e-12: {mp.nstr(matern_q(r, d, g) / (paper * log(1 / r)), 6)}")
d, g = 1, mpf(3) / 4
p0 = 2 ** (mpf(d) / 2) * gamma((2 * g - d) / 2) / (2 ** d * pi ** (mpf(d) / 2) * gamma(g))
check("d=1 gamma=3/4: finite regime, 2^(d/2) Gamma((alpha-n)/2)/(2^n pi^(n/2) Gamma(alpha/2)) = p(0)",
      abs(p0 - matern_q(mpf(10) ** (-12), d, g)) < mpf(10) ** (-5), f"p(0) = {mp.nstr(p0, 8)}")

print("\n== F. the map phi -> F and one dimension walk ==")
# (1-t)_+ in Phi_1 (Polya). In Phi_2 it would need int_0^1 (1-t) J_0(s t) t dt >= 0 for all s.
vals = [(s, quad(lambda t: (1 - t) * besselj(0, s * t) * t, [0, 1])) for s in [mpf(x) for x in range(2, 16)]]
neg = [(s, v) for s, v in vals if v < 0]
check("(1-t)_+ is not in Phi_2: its plane Hankel transform is negative somewhere", len(neg) > 0,
      "e.g. s=%s: %s" % (mp.nstr(neg[0][0], 3), mp.nstr(neg[0][1], 6)) if neg else "")
# and its line transform is nonnegative: 2(1 - cos s)/s^2
check("(1-t)_+ is in Phi_1: int_0^1 (1-t) cos(st) dt = (1 - cos s)/s^2 >= 0",
      all(abs(quad(lambda t: (1 - t) * cos(s * t), [0, 1]) - (1 - cos(s)) / s ** 2) < mpf(10) ** (-15)
          for s in [mpf(3), mpf(7)]))
# F(r) = int_0^r (1 - phi(u)) du/u for phi = (1-t)_+ : r for r <= 1, 1 + log r for r >= 1; rF'(r) = 1 - phi(r)
Fphi = lambda r: r if r <= 1 else 1 + log(r)
check("phi = (1-t)_+: F(r) = r (r<=1), 1 + log r (r>=1); F(a r) - F(r) -> log a (c = 1)",
      abs(Fphi(mpf(2000)) - Fphi(mpf(1000)) - log(2)) < mpf(10) ** (-18))

# Schoenberg's Omega_d (the transform of the uniform law on the unit sphere of R^d) is in Phi_d and
# not in Phi_(d+1): every member of Phi_n is a mixture of dilates of Omega_n, so it is >= inf Omega_n,
# and inf Omega_d < inf Omega_(d+1). Through the map this is the step profile k_d = c 1_(0,tau).
from mpmath import besseljzero

infs = []
for d in range(1, 8):
    if d == 1:
        infs.append(mpf(-1))
    else:
        t = besseljzero(mpf(d) / 2, 1)  # Omega_d' = -(t/d) Omega_(d+2): first minimum at j_{d/2,1}
        infs.append(Omega(d, t))
check("inf Omega_d increases strictly with d (so Omega_d is not in Phi_(d+1))",
      all(infs[i] < infs[i + 1] for i in range(len(infs) - 1)),
      "inf: " + " ".join(mp.nstr(v, 5) for v in infs))
# the Cin ray on the line is phi = cos: cos is not in Phi_2 because min cos = -1 < inf J_0
check("cos is not in Phi_2: -1 < inf J_0", mpf(-1) < infs[1], f"inf J_0 = {mp.nstr(infs[1], 6)}")

print("\n== G. the constants of Cygan-Grzywny-Trojan's Theorems 8-9 and Corollaries 3-4 ==")
for d, a in [(3, mpf(1) / 2), (3, mpf(2)), (5, mpf(3) / 2)]:
    Ct = 2 ** (-a) * gamma((mpf(d) - a) / 2) / (gamma(mpf(d) / 2) * gamma(1 + a / 2))
    At = 2 ** (-a) * pi ** (-mpf(d) / 2) * gamma((mpf(d) - a) / 2) / gamma(a / 2)
    check(f"d={d} alpha={a}: C~ = paper's ball constant, A~ = R(d,alpha)",
          abs(Ct / ball_const(d, a) - 1) < mpf(10) ** (-18) and abs(At / R(d, a) - 1) < mpf(10) ** (-18))

print("\n== H. Leonenko-Olenko 2013: c_1(n,alpha) (Theorems 2, 3) and c_2(n,alpha) (Theorem 4) ==")


def c1(n, a):
    return 2 ** a * gamma(a / 2 + 1) * gamma(mpf(n) / 2) / gamma((mpf(n) - a) / 2)


def c2(n, a):
    return 2 ** a * pi ** (mpf(n) / 2) * gamma(a / 2) / gamma((mpf(n) - a) / 2)


for n in [1, 2, 3, 4, 5, 9]:
    for a in [mpf(1) / 10, mpf(3) / 10, mpf(4) / 5, mpf(3) / 2, mpf(5) / 2]:
        if a < n:
            check(f"n={n} alpha={a}: 1/c_1 = R(d,c)|S|/c and 1/c_2 = R(d,c)",
                  abs(1 / c1(n, a) / ball_const(n, a) - 1) < mpf(10) ** (-18)
                  and abs(1 / c2(n, a) / R(n, a) - 1) < mpf(10) ** (-18))
a = mpf(3) / 5
check("Remark 1: c_1(1,alpha) = Gamma(1+alpha) cos(alpha pi/2)",
      abs(c1(1, a) - gamma(1 + a) * cos(a * pi / 2)) < mpf(10) ** (-18))
check("Remark 2: c_2(1,alpha) = 2 Gamma(alpha) cos(alpha pi/2), so 1/c_2(1,c) is the paper's R(1,c)",
      abs(c2(1, a) - 2 * gamma(a) * cos(a * pi / 2)) < mpf(10) ** (-18))
# Theorem 3, the direction (a) => (b), where Theorem 2 does not apply (alpha <= (n-3)/2):
# B(r) = (1 + r^2/2)^(-gamma), G(lambda) = mu(B_lambda); G(lambda) c_1(n,alpha) / B(1/lambda) -> 1.
for d, g in [(4, mpf(3) / 20), (5, mpf(2) / 5), (9, mpf(1))]:
    row = [ball_direct(s, d, g) * c1(d, 2 * g) / chi(1 / s, g) for s in [mpf(10) ** (-2), mpf(10) ** (-4)]]
    check(f"n={d} alpha={2*g} <= (n-3)/2: G(lambda) c_1 / B(1/lambda) -> 1 (Theorem 3 without monotonicity)",
          abs(row[-1] - 1) < mpf(1) / 1000, "  ".join(mp.nstr(x, 10) for x in row))
# Example 3 of the paper: B(r) = (1+r^2)^(-kappa/2), g(lambda) of (8) = Aronszajn-Smith's G_kappa
n_, k_, lam = 6, mpf(4), mpf(3) / 10
g8 = besselk((n_ - k_) / 2, lam) * lam ** ((k_ - n_) / 2) / (
    pi ** (mpf(n_) / 2) * 2 ** ((n_ + k_ - 2) / 2) * gamma(k_ / 2))
check("Example 3, (8): the Bessel spectral density is Aronszajn-Smith's G_kappa",
      abs(g8 / G(k_, lam, n_) - 1) < mpf(10) ** (-18))

print("\nALL PASS" if OK else "\nSOME CHECK FAILED")
