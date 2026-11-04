"""Q-0423, review round 1 of the isotropic paper, required change 7: the slowly varying factor.

Setting (def:isotropic-origin-datum, lem:isotropic-exponent-log, prop:origin-rate-d). An isotropic
origin datum (0, k_d) in dimension d, k_d nonincreasing on (0, infinity), c = k_d(0+) in
(0, infinity), C_k = int_1^infty k_d(r) dr/r < infinity. Its exponent is

    F_d(xi) = int (1 - cos<xi,x>) nu_d(dx)
            = (1/|S^{d-1}|) int_{S^{d-1}} phi(<xi,eta>) sigma(d eta),
    phi(s)  = int_0^infty (1 - cos(r s)) k_d(r) dr/r,

and mu-hat(rho e) = exp(-F_d(rho e)) = rho^{-c} L(rho).

The claim checked: with K(x) = exp( int_x^1 (c - k_d(u)) du/u ) and

    kappa_d = gamma_E + (1/2) [psi(1/2) - psi(d/2)]        (psi the digamma function),
    A(d, c, C_k) = exp(-C_k - c kappa_d),

    L(rho) / ( A(d, c, C_k) K(1/rho) ) -> 1   as rho -> infinity.

Parts.
 0. The constants: E log|eta_1| for eta uniform on S^{d-1} against (1/2)[psi(1/2) - psi(d/2)];
    Cin(1) + Ci(1) against gamma_E; and the constant of the sphere-averaged kernel
    Omega_d(s) = E cos(s eta_1) = Gamma(d/2) (2/s)^{d/2-1} J_{d/2-1}(s),
    int_0^1 (1 - Omega_d(u)) du/u - int_1^infty Omega_d(u) du/u, against kappa_d.
 1. Method A against method B. Method A is the definition taken literally: phi by quadrature of
    the cosine integral, then the average over the sphere by a second quadrature. Method B is the
    single integral F_d(rho e) = int_0^infty (1 - Omega_d(r rho)) k_d(r) dr/r, split at r = 1/rho
    and r = 1; the oscillatory middle piece int_1^rho Omega_d(u) k_d(u/rho) du/u is integrated on
    the real axis up to u = X0 = 200 and, beyond, moved to two vertical contours, on which the
    integrands decay like e^{-t} (so method B reaches rho = 10^60). Agreement at moderate rho is
    the check that B computes the paper's F_d, with the paper's normalisation of k_d.
 2. Three profiles supported in (0,1), so C_k = 0:
      step     k_d = c 1_(0,1)                         K = 1 on (0,1)
      power    k_d = c (1 - r^beta) 1_(0,1)            K(x) = exp(c (1 - x^beta)/beta), bounded
      log      k_d = c (1 - 1/log(e/r)) 1_(0,1)        K(x) = (1 + log(1/x))^c, unbounded
    For each, d = 1, 2, 3 and delta(rho) := [F_d(rho e) - c log rho + log K(1/rho)]/c - kappa_d,
    which does not depend on c because F_d is linear in k_d. The ratio of the claim is
    exp(-c delta(rho)); it is tabulated at c = 1. (The brief's example k_d = c(1 + 1/log(e/r)) is
    increasing; the nonincreasing profile with the same K up to inversion is the one used.)
 3. The Matern datum of the paper (prop:isotropic-bridge(2)): mu-hat = (1 + rho^2/2)^(-gamma),
    c = 2 gamma, delay profile k_I(u) = gamma e^{-u}, polar profile by eq:polar-profile-d,
        k_d(r) = (4 gamma / Gamma(d/2)) (r/sqrt 2)^{d/2} K_{d/2}(sqrt 2 r)
    (K_nu the modified Bessel function). C_k is not 0 and L is known exactly:
    L(rho) = rho^{2 gamma} (1 + rho^2/2)^{-gamma} -> 2^gamma.
    Checked: (a) k_d reproduces the exponent gamma log(1 + rho^2/2) through the definition;
    (b) A K(0+) = 2^gamma; (c) the ratio L(rho)/(A K(1/rho)); (d) the rate: the closed-form
    density eq:matern-density against Q s^{c-d} K(s), Q = R(d,c) A.

Run from the repository root:
    uv run --no-project --with mpmath python \
        records/affine/reviews/verify-round1-scripts/b_slowly_varying_factor.py \
        > records/affine/reviews/verify-round1-scripts/b_slowly_varying_factor-output.txt
"""
import sys
import time

from mpmath import (besselj, besselk, cos, digamma, euler, exp, gamma, inf, log, mp, mpc, mpf, pi,
                    quad, quadosc, sin, sqrt)

J = mpc(0, 1)
X0 = 200          # beyond this abscissa the oscillatory integrals are taken on vertical contours
DPS0 = 40         # working precision of everything except the contour at rho, for huge rho


def ns(x, n=12):
    return mp.nstr(x, n)


# ----------------------------------------------------------------------------------------------
# constants
# ----------------------------------------------------------------------------------------------
def kappa(d):
    """gamma_E + E log|eta_1| = gamma_E + (1/2)[psi(1/2) - psi(d/2)]."""
    return euler + (digamma(mpf(1) / 2) - digamma(mpf(d) / 2)) / 2


def A_const(d, c, Ck):
    return exp(-Ck - c * kappa(d))


def rate_const(d, c):
    """R(d,c) of prop:origin-rate-d."""
    return gamma((mpf(d) - c) / 2) / (mpf(2) ** c * pi ** (mpf(d) / 2) * gamma(mpf(c) / 2))


def Omega(d, u):
    """E cos(u eta_1), eta uniform on S^{d-1}."""
    if d == 1:
        return cos(u)
    if d == 3:
        return sin(u) / u
    nu = mpf(d) / 2 - 1
    return gamma(mpf(d) / 2) * (2 / u) ** nu * besselj(nu, u)


def Hup(d, z):
    """Analytic in Re z > 0, Omega_d(u) = Re Hup(d, u) for u > 0, |Hup(d, a + it)| = O(e^{-t})."""
    if d == 1:
        return exp(J * z)
    if d == 3:
        return -J * exp(J * z) / z
    # Gamma(d/2) (2/z)^nu H^(1)_nu(z), with H^(1)_nu(z) = (2/(pi i)) e^{-i nu pi/2} K_nu(-i z)
    nu = mpf(d) / 2 - 1
    return gamma(mpf(d) / 2) * (2 / z) ** nu * 2 / (pi * J) * exp(-J * nu * pi / 2) * besselk(nu, -J * z)


def breakpoints_exp():
    """Breakpoints for int_0^infty e^{-t}(...) dt, truncated where e^{-t} < 10^-(dps+5)."""
    T = (mp.dps + 5) * log(10)
    pts = [mpf(0), mpf(1)]
    while pts[-1] < T:
        pts.append(pts[-1] * 2)
    return pts


def tail(d, g, a):
    """int_a^infty Omega_d(u) g(u) du for g analytic in {Re u >= a, Im u >= 0}, real on the real
    axis, of polynomial growth: Re( i int_0^infty Hup(a + it) g(a + it) dt )."""
    a = mpf(a)
    val = quad(lambda t: Hup(d, a + J * t) * g(a + J * t), breakpoints_exp())
    return (J * val).real


def osc(d, g, a, b):
    """int_a^b Omega_d(u) g(u) du, 0 < a < b <= infinity: on the real axis up to min(b, X0), on
    pieces of length pi; beyond X0 as tail(X0) - tail(b). The contour at b is computed with enough
    digits to resolve b modulo 2 pi."""
    a = mpf(a)
    top = b if b <= X0 else mpf(X0)
    total = mpf(0)
    if a < top:
        pts = [a]
        while pts[-1] + pi < top:
            pts.append(pts[-1] + pi)
        pts.append(top)
        total += quad(lambda u: Omega(d, u) * g(u), pts)
    else:
        top = a
    if b > top:
        total += tail(d, g, top)
        if b != inf:
            old = mp.dps
            try:
                mp.dps = max(old, int(mp.log10(b)) + 40)
                tb = tail(d, g, b)
            finally:
                mp.dps = old
            total -= tb
    return total


# ----------------------------------------------------------------------------------------------
# profiles supported in (0,1)
# ----------------------------------------------------------------------------------------------
class Profile:
    def __init__(self, name, k_over_c, logK_over_c):
        self.name = name
        self.k = k_over_c          # r -> k_d(r)/c on (0,1), analytic in r
        self.logK = logK_over_c    # x -> log K(x) / c on (0,1]


BETA = mpf(1) / 2
STEP = Profile("step: k_d = c 1_(0,1); K = 1",
               lambda r: mpf(1) + 0 * r, lambda x: mpf(0))
POWER = Profile("power: k_d = c (1 - r^(1/2)) 1_(0,1); K(x) = exp(2c (1 - x^(1/2)))",
                lambda r: 1 - r ** BETA, lambda x: (1 - x ** BETA) / BETA)
LOGP = Profile("log: k_d = c (1 - 1/log(e/r)) 1_(0,1); K(x) = (1 + log(1/x))^c",
               lambda r: 1 - 1 / (1 - log(r)), lambda x: log(1 + log(1 / x)))


def F_method_B(d, prof, rho):
    """F_d(rho e)/c by the single integral with Omega_d, split at r = 1/rho and r = 1.
    Returns (F/c, rest/c) with rest = F - c log rho + log K(1/rho)."""
    rho = mpf(rho)

    def head(u):
        if u == 0:
            return mpf(0)
        return (1 - Omega(d, u)) * prof.k(u / rho) / u

    p1 = quad(head, [0, mpf(1) / 4, 1])
    g = lambda u: prof.k(u / rho) / u
    p3 = osc(d, g, 1, rho)                     # int_1^rho Omega_d(u) k(u/rho) du/u
    rest = p1 - p3
    return rest + log(rho) - prof.logK(1 / rho), rest


def phi_literal(prof, s):
    """phi(s)/c = int_0^1 (1 - cos(r s)) k(r) dr/r, by quadrature on pieces of length <= pi/s."""
    s = abs(s)
    if s == 0:
        return mpf(0)
    n = max(2, int(s / pi) + 2)
    pts = [mpf(j) / n for j in range(n + 1)]

    def f(r):
        if r == 0:
            return mpf(0)
        return (1 - cos(r * s)) * prof.k(r) / r

    return quad(f, pts)


def F_method_A(d, prof, rho):
    """F_d(rho e)/c from the definition: the average of phi(rho eta_1) over the unit sphere."""
    rho = mpf(rho)
    if d == 1:
        return phi_literal(prof, rho)
    n = max(4, int(rho / pi) + 4)
    if d == 2:
        pts = [pi / 2 * mpf(j) / n for j in range(n + 1)]
        return 2 / pi * quad(lambda th: phi_literal(prof, rho * cos(th)), pts)
    # d >= 3: density of eta_1 on (-1,1) is Gamma(d/2)/(sqrt(pi) Gamma((d-1)/2)) (1-t^2)^((d-3)/2)
    cst = 2 * gamma(mpf(d) / 2) / (sqrt(pi) * gamma(mpf(d - 1) / 2))
    pts = [mpf(j) / n for j in range(n + 1)]
    return cst * quad(lambda t: phi_literal(prof, rho * t) * (1 - t * t) ** (mpf(d - 3) / 2), pts)


# ----------------------------------------------------------------------------------------------
# the Matern datum
# ----------------------------------------------------------------------------------------------
def matern_k(d, gam, r):
    """eq:polar-profile-d at k_I(u) = gam e^{-u}."""
    hd = mpf(d) / 2
    return 4 * gam / gamma(hd) * (r / sqrt(2)) ** hd * besselk(hd, sqrt(2) * r)


def matern_logK(d, gam, x):
    """log K(x) = int_x^1 (c - k_d(u)) du/u, c = 2 gam."""
    c = 2 * gam
    pts = [mpf(1)]
    while pts[-1] > x:
        pts.append(max(x, pts[-1] / 10))
    pts = pts[::-1]
    if len(pts) == 1:
        return mpf(0)
    return quad(lambda u: (c - matern_k(d, gam, u)) / u, pts)


def matern_logK0(d, gam):
    c = 2 * gam
    pts = [mpf(10) ** (-j) for j in range(0, 40, 2)][::-1]
    return quad(lambda u: (c - matern_k(d, gam, u)) / u, [mpf(0)] + pts)


def matern_Ck(d, gam):
    return quad(lambda r: matern_k(d, gam, r) / r, [1, 2, 4, 8, 16, 32, 64, inf])


def matern_density(d, gam, x):
    """eq:matern-density."""
    nu = gam - mpf(d) / 2
    return 2 / ((2 * pi) ** (mpf(d) / 2) * gamma(gam)) * (x / sqrt(2)) ** nu * besselk(nu, sqrt(2) * x)


# ----------------------------------------------------------------------------------------------
def part0():
    mp.dps = 30
    print("PART 0. The constants")
    print("  (a) E log|eta_1|, eta uniform on S^{d-1}, by quadrature, against (1/2)[psi(1/2) - psi(d/2)]:")
    for d in range(2, 8):
        if d == 2:
            num = 2 / pi * quad(lambda th: log(cos(th)), [0, pi / 4, pi / 2])
        else:
            cst = 2 * gamma(mpf(d) / 2) / (sqrt(pi) * gamma(mpf(d - 1) / 2))
            num = cst * quad(lambda t: log(t) * (1 - t * t) ** (mpf(d - 3) / 2), [0, mpf(1) / 2, 1])
        cl = (digamma(mpf(1) / 2) - digamma(mpf(d) / 2)) / 2
        print(f"      d = {d}: quadrature {ns(num, 18):>22}   closed form {ns(cl, 18):>22}   "
              f"difference {ns(num - cl, 3)}")
    print("      (d = 1: eta_1 = +-1, E log|eta_1| = 0 = (1/2)[psi(1/2) - psi(1/2)];"
          " d = 2: -log 2; d = 3: -1.)")
    one = quad(lambda u: (1 - cos(u)) / u, [0, 1]) - quadosc(lambda u: cos(u) / u, [1, inf], omega=1)
    print(f"  (b) int_0^1 (1 - cos u) du/u - int_1^infty cos u du/u = {ns(one, 20)}")
    print(f"      Euler's constant gamma_E                           = {ns(+euler, 20)}")
    print("  (c) kappa_d = gamma_E + (1/2)[psi(1/2) - psi(d/2)] against")
    print("      int_0^1 (1 - Omega_d(u)) du/u - int_1^infty Omega_d(u) du/u (Omega_d = E cos(u eta_1)):")
    for d in range(1, 8):
        head = quad(lambda u: (1 - Omega(d, u)) / u if u != 0 else mpf(0), [0, mpf(1) / 4, 1])
        tl = osc(d, lambda u: 1 / u, 1, inf)
        print(f"      d = {d}: integral {ns(head - tl, 18):>22}   kappa_d {ns(kappa(d), 18):>22}   "
              f"difference {ns(head - tl - kappa(d), 3)}")
    print(f"      exp(-kappa_d), the limit of L for the unit step at c = 1: "
          + ", ".join(f"d={d}: {ns(exp(-kappa(d)), 10)}" for d in (1, 2, 3)))
    print()


def part1():
    print("PART 1. Method A (the definition: cosine integral, then the sphere average, two nested")
    print("quadratures at 18 digits) against method B (one integral with Omega_d, at 40 digits).")
    print("F_d(rho e)/c:")
    print(f"  {'profile':>6} {'d':>2} {'rho':>5} {'method A':>22} {'method B':>22} {'A - B':>10}")
    for prof, tag in ((STEP, "step"), (POWER, "power"), (LOGP, "log")):
        for d in (1, 2, 3):
            for rho in (3, 12, 30):
                mp.dps = 18
                a = F_method_A(d, prof, rho)
                mp.dps = DPS0
                b = F_method_B(d, prof, rho)[0]
                print(f"  {tag:>6} {d:2d} {rho:5d} {ns(a, 18):>22} {ns(b, 18):>22} {ns(a - b, 3):>10}")
                sys.stdout.flush()
    mp.dps = DPS0
    print("  the contour beyond X0 = 200 against the real axis, method B at rho = 1000 with X0 = 200")
    print("  and with X0 = 2000 (no contour), log profile:")
    global X0
    for d in (1, 2, 3):
        b1 = F_method_B(d, LOGP, 1000)[0]
        X0 = 2000
        b2 = F_method_B(d, LOGP, 1000)[0]
        X0 = 200
        print(f"    d = {d}: {ns(b1, 20):>24} {ns(b2, 20):>24}   difference {ns(b1 - b2, 3)}")
    print()


def part2():
    print("PART 2. delta(rho) = [F_d(rho e) - c log rho + log K(1/rho)]/c - kappa_d  (method B),")
    print("and the ratio L(rho) / (A K(1/rho)) = exp(-c delta(rho)) at c = 1. C_k = 0 for these profiles.")
    exps = (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 60)
    for prof in (STEP, POWER, LOGP):
        print(f"  Profile {prof.name}")
        islog = prof is LOGP
        for d in (1, 2, 3):
            extra = f" {'delta (1 + log rho)':>20}" if islog else ""
            print(f"    d = {d}, kappa_d = {ns(kappa(d), 12)}")
            print(f"    {'rho':>7} {'delta(rho)':>16} {'ratio at c = 1':>18}{extra}")
            for e in exps:
                mp.dps = DPS0
                rho = mpf(10) ** e
                rest = F_method_B(d, prof, rho)[1]
                delta = rest - kappa(d)
                line = f"    {'1e' + str(e):>7} {ns(delta, 6):>16} {ns(exp(-delta), 12):>18}"
                if islog:
                    line += f" {ns(delta * (1 + log(rho)), 8):>20}"
                print(line)
                sys.stdout.flush()
            if islog:
                print(f"    (first-order prediction: delta (1 + log rho) -> -kappa_d = {ns(-kappa(d), 8)})")
        print()


def part3():
    mp.dps = 30
    print("PART 3. The Matern datum: mu-hat(rho e) = (1 + rho^2/2)^(-gamma), c = 2 gamma,")
    print("k_d(r) = (4 gamma/Gamma(d/2)) (r/sqrt 2)^(d/2) K_{d/2}(sqrt 2 r).")
    cases = ((1, mpf("0.3")), (2, mpf("0.75")), (3, mpf("0.75")), (3, mpf("1.25")), (5, mpf("1.0")),
             (2, mpf("2.0")))
    print("  (a) k_d reproduces the exponent: int_0^infty (1 - Omega_d(r rho)) k_d(r) dr/r against")
    print("      gamma log(1 + rho^2/2), at rho = 3; and k_d(0+) against 2 gamma:")
    for d, gam in cases:
        rho = mpf(3)
        pts = [mpf(j) / 2 for j in range(0, 121)]
        num = quad(lambda r: (1 - Omega(d, r * rho)) * matern_k(d, gam, r) / r if r != 0 else mpf(0), pts)
        ex = gam * log(1 + rho ** 2 / 2)
        k0 = matern_k(d, gam, mpf(10) ** (-12))
        print(f"      d = {d}, gamma = {ns(gam, 4)}: {ns(num, 16):>20} vs {ns(ex, 16):>20}  "
              f"(difference {ns(num - ex, 3)});  k_d(1e-12) = {ns(k0, 12)}, 2 gamma = {ns(2 * gam, 12)}")
    print("  (b) C_k, log K(0+), and A(d,c,C_k) K(0+) against lim L = 2^gamma:")
    data = {}
    for d, gam in cases:
        c = 2 * gam
        Ck = matern_Ck(d, gam)
        lK0 = matern_logK0(d, gam)
        A = A_const(d, c, Ck)
        data[(d, gam)] = (Ck, lK0, A)
        print(f"      d = {d}, gamma = {ns(gam, 4)}, c = {ns(c, 4)}: C_k = {ns(Ck, 14)}, log K(0+) = {ns(lK0, 14)}, "
              f"A = {ns(A, 14)}, A K(0+) = {ns(A * exp(lK0), 16)}, 2^gamma = {ns(mpf(2) ** gam, 16)}")
    print("  (c) the ratio L(rho) / (A K(1/rho)), L(rho) = rho^(2 gamma) (1 + rho^2/2)^(-gamma):")
    exps = (0, 1, 2, 3, 4, 6, 8)
    print(f"      {'d':>2} {'gamma':>6} " + " ".join(f"{'rho=1e' + str(e):>16}" for e in exps))
    for d, gam in cases:
        Ck, lK0, A = data[(d, gam)]
        cells = []
        for e in exps:
            rho = mpf(10) ** e
            L = rho ** (2 * gam) * (1 + rho ** 2 / 2) ** (-gam)
            K = exp(matern_logK(d, gam, 1 / rho))
            cells.append(f"{ns(L / (A * K), 12):>16}")
        print(f"      {d:2d} {ns(gam, 4):>6} " + " ".join(cells))
        sys.stdout.flush()
    print("  (d) the rate, for c = 2 gamma < d: the density eq:matern-density over Q s^(c-d) K(s),")
    print("      Q = R(d,c) A(d,c,C_k) = Gamma((d-c)/2) exp(-C_k - (c/2)(gamma_E - psi(d/2))) / (pi^(d/2) Gamma(c/2)):")
    exps = (0, 1, 2, 3, 4, 6, 8)
    print(f"      {'d':>2} {'gamma':>6} {'Q':>16} " + " ".join(f"{'s=1e-' + str(e):>16}" for e in exps))
    for d, gam in cases:
        c = 2 * gam
        if not c < d:
            continue
        Ck, lK0, A = data[(d, gam)]
        Q = rate_const(d, c) * A
        Q2 = gamma((d - c) / 2) * exp(-Ck - c / 2 * (euler - digamma(mpf(d) / 2))) / (pi ** (mpf(d) / 2) * gamma(c / 2))
        assert abs(Q / Q2 - 1) < mpf(10) ** (-25)
        cells = []
        for e in exps:
            s = mpf(10) ** (-e)
            cells.append(f"{ns(matern_density(d, gam, s) / (Q * s ** (c - d) * exp(matern_logK(d, gam, s))), 12):>16}")
        print(f"      {d:2d} {ns(gam, 4):>6} {ns(Q, 12):>16} " + " ".join(cells))
        sys.stdout.flush()
    print()


def part4():
    mp.dps = 30
    print("PART 4. The line, d = 1, against Sato-Yamazato (1.8) / Sato (53.27) and Theorem 1.7(i) / (53.28).")
    print("  kappa_1 = gamma_E, so A(1, c, C_k) = exp(-c gamma_E - C_k), which is their constant c / kappa:")
    lhs = quad(lambda u: (exp(-u) - 1) / u, [0, 1]) + quad(lambda u: exp(-u) / u, [1, inf])
    print(f"    int_0^1 (e^-u - 1) du/u + int_1^infty e^-u du/u = {ns(lhs, 20)},  -gamma_E = {ns(-euler, 20)}")
    print("  the constant of the density for a symmetric law, lambda_+ = c/2, N = 0:")
    print("    sin(c pi/2) / (Gamma(c) sin(c pi)) against R(1, c):")
    for c in (mpf("0.2"), mpf("0.5"), mpf("0.8"), mpf("0.95")):
        sy = sin(c * pi / 2) / (gamma(c) * sin(c * pi))
        print(f"    c = {ns(c, 3)}: {ns(sy, 16):>20}   R(1,c) = {ns(rate_const(1, c), 16):>20}   "
              f"difference {ns(sy - rate_const(1, c), 3)}")
    print()


def main():
    t0 = time.time()
    part0()
    part4()
    part1()
    part2()
    part3()
    print(f"(elapsed: {time.time() - t0:.0f} s)")


if __name__ == "__main__":
    main()
