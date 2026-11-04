"""Blind check of claim (iii): a Bochner test of the residual, for the two cases the point-set
search of c_filtration_residual_pd.py did not decide.

If F is in A_D, then for every lambda in (0,1) the residual
    R(xi) = exp(-(F(|xi|) - F(lambda |xi|))),  xi in R^D,
is the characteristic function of a probability measure rho on R^D. Then for every nonnegative
integrable W with integrable transform What(xi) = int W(x) e^(-i<xi,x>) dx,
    T(W) := (2 pi)^(-D) int_(R^D) What(xi) R(xi) dxi = int W d rho >= 0.
So one W >= 0 with T(W) < 0 excludes F from A_D. Test functions: the radial shells
    W(x) = N |x|^(2p) e^(-a |x|^2),  int W = 1,
    What(xi) = L_p^(D/2-1)(|xi|^2/4a) e^(-|xi|^2/4a) / L_p^(D/2-1)(0)       (checked below by quadrature),
with peak radius s0 = sqrt(p/a). W(0) = 0, so the constant lambda^c = R(infinity) may be subtracted.

To first order in the residual's Levy measure, rho = lambda^c (delta_0 + nu_res + ...), with
nu_res of polar profile k_D(s) - k_D(s/lambda), k_D the profile that dimension D needs. So T(W)
should be close to
    P1(W) := lambda^c int_0^oo W(s) (k_D(s) - k_D(s/lambda)) ds/s
when W sits away from the origin (the next term is of order log(1/lambda)^2). The agreement of T
with P1 checks the profile computation against the definition; the sign of T is the test.

Cases (c = 1):
  1. phi = sin u/u, D = 4: needs k_4 = (2 - r^2)/(2 sqrt(1 - r^2)) 1_(0,1), increasing. Expect T < 0.
  2. phi = sin u/u, D = 3: k_3 = 1_(0,1). Control, expect T >= 0.
  3. phi = (1-u)_+ (Euclid's hat h_1), D = 2: needs k_2(s) = (1/s) int_0^s J_0, not monotone. Expect T < 0
     for a shell where k_2 increases.
  4. the same, D = 1: control, expect T >= 0.

Run: uv run --no-project --with mpmath --with scipy python c_filtration_bochner_test.py
"""
from mpmath import (mp, mpf, pi, sqrt, exp, log, sin, cos, gamma, loggamma, laguerre, besselj, struveh,
                    ci, euler, quad, binomial)

mp.dps = 30


def Omega(d, t):
    if t == 0:
        return mpf(1)
    if d == 1:
        return cos(t)
    nu = mpf(d - 2) / 2
    return gamma(mpf(d) / 2) * (2 / t) ** nu * besselj(nu, t)


def sphere(D):
    return 2 * pi ** (mpf(D) / 2) / gamma(mpf(D) / 2)


def F_sinc(r):  # int_0^r (1 - sin u/u) du/u = Cin(r) + sin r/r - 1
    if r == 0:
        return mpf(0)
    if r < mpf("0.05"):
        return r ** 2 / 12 - r ** 4 / 480 + r ** 6 / 30240 - r ** 8 / 2903040
    return euler + log(r) - ci(r) + sin(r) / r - 1


def F_hat(r):  # int_0^r (1 - (1-u)_+) du/u
    return r if r <= 1 else 1 + log(r)


class Shell:
    def __init__(self, D, p, s0):
        self.D, self.p, self.a = D, p, mpf(p) / mpf(s0) ** 2
        self.alpha = mpf(D) / 2 - 1
        self.L0 = binomial(p + self.alpha, p)
        self.logN = (p + mpf(D) / 2) * log(self.a) + loggamma(mpf(D) / 2) \
            - (mpf(D) / 2) * log(pi) - loggamma(p + mpf(D) / 2)

    def W(self, s):  # the value of W at radius s
        if s == 0:
            return mpf(0)
        return exp(self.logN + 2 * self.p * log(s) - self.a * s * s)

    def What(self, r):
        x = r * r / (4 * self.a)
        return laguerre(self.p, self.alpha, x) * exp(-x) / self.L0

    def rmax(self):
        return sqrt(4 * self.a * 130)

    def check_transform(self):
        """What against the radial integral |S^(D-1)| int W(s) Omega_D(r s) s^(D-1) ds, at two points."""
        s0 = sqrt(self.p / self.a)
        w = s0 / (2 * sqrt(mpf(self.p)))
        for r in (mpf("0.3") / w, mpf(2) / s0):
            lo, hi = max(mpf(0), s0 - 12 * w), s0 + 12 * w
            n = int((hi - lo) * r / 2) + 8
            num = sphere(self.D) * quad(lambda s: self.W(s) * Omega(self.D, r * s) * s ** (self.D - 1),
                                        [lo + (hi - lo) * mpf(i) / n for i in range(n + 1)])
            assert abs(num - self.What(r)) < mpf(10) ** (-12), (num, self.What(r))


def T(F, lam, sh, kinks=()):
    D = sh.D
    rm = sh.rmax()
    n = max(80, 4 * sh.p)
    nodes = sorted(set([rm * mpf(i) / n for i in range(n + 1)] + [mpf(k) for k in kinks if k < rm]))
    f = lambda r: sh.What(r) * (exp(-(F(r) - F(lam * r))) - lam) * r ** (D - 1)
    return sphere(D) / (2 * pi) ** D * quad(f, nodes, method="gauss-legendre")


def P1(k, lam, sh, breaks):
    """lambda int W(s) (k(s) - k(s/lambda)) ds/s, with the integration cut at `breaks`."""
    f = lambda s: sh.W(s) * (k(s) - k(s / lam)) / s if s > 0 else mpf(0)
    return lam * quad(f, breaks)


print("Bochner test of the residual: T(W) = int W d rho if the residual is a law; T < 0 excludes it")

# ------------------------------------------------------------------------------- cases 1, 2
print("\n1-2. phi = sin u/u.  D = 4 needs k_4 = (2 - r^2)/(2 sqrt(1 - r^2)) on (0,1); D = 3 has k_3 = 1_(0,1)")
k4 = lambda s: (2 - s * s) / (2 * sqrt(1 - s * s)) if 0 < s < 1 else mpf(0)
k3 = lambda s: mpf(1) if 0 < s < 1 else mpf(0)
for lam in (mpf("0.9"), mpf("0.97")):
    for p, s0 in ((4, mpf("0.55")), (8, mpf("0.6"))):
        sh4, sh3 = Shell(4, p, s0), Shell(3, p, s0)
        sh4.check_transform()
        sh3.check_transform()
        t4 = T(F_sinc, lam, sh4)
        p4 = P1(k4, lam, sh4, [0, lam / 2, lam, (1 + lam) / 2, 1])
        t3 = T(F_sinc, lam, sh3)
        p3 = P1(k3, lam, sh3, [0, lam, 1])
        print(f"  lambda = {mp.nstr(lam, 3)}, shell p = {p}, s0 = {mp.nstr(s0, 3)}:"
              f"  D = 4: T = {mp.nstr(t4, 8)}  (first order P1 = {mp.nstr(p4, 8)})"
              f"   D = 3: T = {mp.nstr(t3, 8)}  (P1 = {mp.nstr(p3, 8)})")
        assert t4 < 0 and t3 > 0
print("  D = 4: T < 0, the residual is not a law on R^4: F_phi is not in A_4.  D = 3: T > 0 (control).")

# ------------------------------------------------------------------------------- cases 3, 4
print("\n3-4. phi = (1-u)_+ (Euclid's hat h_1).  The plane needs k_2(s) = (1/s) int_0^s J_0(u) du")


def k2(s):
    if s == 0:
        return mpf(1)
    # int_0^s J_0 = s J_0(s) + (pi s/2) (J_1(s) H_0(s) - J_0(s) H_1(s))
    return besselj(0, s) + pi / 2 * (besselj(1, s) * struveh(0, s) - besselj(0, s) * struveh(1, s))


chk = quad(lambda u: besselj(0, u), [0, 2, 4, 6, 7]) / 7
assert abs(chk - k2(mpf(7))) < mpf(10) ** (-20)
lam = mpf("0.98")
grid = [mpf(i) / 20 for i in range(100, 200)]
gain = [(k2(s / lam) - k2(s), s) for s in grid]
best = max(gain)
print(f"  lambda = {mp.nstr(lam, 3)}: k_2(s/lambda) - k_2(s) is positive for s in"
      f" ({mp.nstr(min(s for g, s in gain if g > 0), 4)}, {mp.nstr(max(s for g, s in gain if g > 0), 4)}),"
      f" largest {mp.nstr(best[0], 5)} at s = {mp.nstr(best[1], 4)}")
s0 = best[1]
for p in (60, 120):
    sh2, sh1 = Shell(2, p, s0), Shell(1, p, s0)
    sh2.check_transform()
    sh1.check_transform()
    t2 = T(F_hat, lam, sh2, kinks=(1, 1 / lam))
    w = s0 / (2 * sqrt(mpf(p)))
    p2 = P1(k2, lam, sh2, [max(mpf("0.01"), s0 - 10 * w), s0 - 3 * w, s0, s0 + 3 * w, s0 + 10 * w])
    t1 = T(F_hat, lam, sh1, kinks=(1, 1 / lam))
    print(f"  shell p = {p}, s0 = {mp.nstr(s0, 4)} (width {mp.nstr(w, 3)}):"
          f"  D = 2: T = {mp.nstr(t2, 8)}  (first order P1 = {mp.nstr(p2, 8)})   D = 1: T = {mp.nstr(t1, 8)}")
    assert t2 < 0 and t1 > 0
print("  D = 2: T < 0, the residual is not a law on the plane: F_phi is not in A_2.  D = 1: T > 0 (control).")
print("\ndone")
