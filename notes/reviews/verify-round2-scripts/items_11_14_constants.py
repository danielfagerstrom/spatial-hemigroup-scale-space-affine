r"""VERIFY round 2, items 11 and 14: three constants.

(11a) The lower bound on the transform. Lemma A.3(1): e^{-F_d(xi)} >= e^{-13c/4 - 2 C_k} |xi|^{-c};
      Proposition A.6(4): e^{-F_d(xi)} >= e^{-13c/4 - C_k} K(1/|xi|) |xi|^{-c}, |xi| >= 1. Both on
      the Matern exponent F(r) = gamma log(1 + r^2/2) in dimension d, with its polar profile, and
      at c = d against the exact coefficient B K(0+) of Proposition 3.17(3).
(11c) B_c of (A.9), I_c / Gamma(1 + c/2) with I_c = (4 pi)^{-d/2} |S^{d-1}| 2^{d-c-1} Gamma((d-c)/2),
      against the constant 2^{-alpha} Gamma((d-alpha)/2) / (Gamma(d/2) Gamma(1 + alpha/2)) of Cygan,
      Grzywny and Trojan, Theorems 8 and 9 (arXiv v2, p. 16), at alpha = c, and against
      R(d,c) |S^{d-1}| / c.
(14)  The plane half of the example w = 4. The cone paper's proof of Lemma 4.12(2) (p. 82) shows
      c z^m (e^{-z} - 2^{-d/2} e^{-z/2}) <= Gamma(m)/2 for every z at c = 4, d = 2 (m = 3/2), from
      the bound z^m (e^{-z} - lambda e^{-z/2}) <= (2m)^m (1 - lambda)^{m+1} / (m+1)^{m+1}, valid
      for m <= 2. With M_2 the supremum of Definition 3.20 this is 4 M_2 <= Gamma(3/2)/2, that is,
      4 <= w_2 = Gamma(3/2) / (2 M_2).

Run: uv run --no-project --with mpmath --with scipy python items_11_14_constants.py
"""
from mpmath import mp, mpf, besselk, gamma, pi, sqrt, quad, inf, exp, log, findroot, diff, nstr, digamma, euler

mp.dps = 25


def k_matern(d, g):
    return lambda r: 4 * g / gamma(mpf(d) / 2) * (r / sqrt(2)) ** (mpf(d) / 2) * besselk(mpf(d) / 2, sqrt(2) * r)


print("(11a) the two lower bounds on rho^c e^{-F(rho)}, Matern, rho >= 1")
for d, g in ((2, mpf(1)), (2, mpf(3) / 4), (3, mpf(3) / 2), (1, mpf(1) / 2)):
    c = 2 * g
    k = k_matern(d, g)
    Ck = quad(lambda r: k(r) / r, [1, 5, 20, inf])
    logK = lambda x: quad(lambda u: (c - k(u)) / u, [x, 1]) if x < 1 else mpf(0)
    b3 = exp(-mpf(13) * c / 4 - 2 * Ck)
    worst3 = worst6 = mpf(10) ** 9
    for rho in (mpf(1), mpf(2), mpf(5), mpf(20), mpf(100), mpf(1000)):
        true = rho ** c * (1 + rho * rho / 2) ** (-g)
        b6 = exp(-mpf(13) * c / 4 - Ck) * exp(logK(1 / rho))
        assert b3 <= b6 <= true
        worst3, worst6 = min(worst3, true / b3), min(worst6, true / b6)
    print(f"  d = {d}, gamma = {nstr(g, 3)}: C_k = {nstr(Ck, 8)}; Lemma A.3(1) constant e^(-13c/4 - 2C_k) = {nstr(b3, 6)};"
          f" Prop. A.6(4) at rho = 1: {nstr(exp(-mpf(13) * c / 4 - Ck), 6)}; both below the transform"
          f" (least ratio true/bound: {nstr(worst3, 5)} and {nstr(worst6, 5)})")
    if c == d:
        area = 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)
        kap = (euler - digamma(mpf(d) / 2)) / 2 - log(2)
        K0 = exp(quad(lambda u: (c - k(u)) / u, [0, mpf("0.01"), 1]))
        B = (2 * pi) ** (-d) * area * exp(-Ck - c * kap)
        print(f"    c = d: printed constant C_* = (2 pi)^(-d) |S| e^(-13d/4 - 2C_k) = {nstr((2*pi)**(-d) * area * b3, 6)};"
              f" with A.6(4): {nstr((2*pi)**(-d) * area * exp(-mpf(13)*d/4 - Ck), 6)};"
              f" the exact coefficient of log(1/s), B K(0+) = {nstr(B * K0, 8)}"
              f" (Example 3.14: 2 (2 pi)^(-d/2)/Gamma(d/2) = {nstr(2 * (2*pi)**(-mpf(d)/2) / gamma(mpf(d)/2), 8)})")

print("(11c) B_c of (A.9) against the constant of Cygan-Grzywny-Trojan, Thms. 8 and 9")
for d, c in ((2, mpf("1.5")), (3, mpf("1.2")), (3, mpf(2)), (5, mpf("0.3")), (1, mpf("0.5"))):
    area = 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)
    Ic = (4 * pi) ** (-mpf(d) / 2) * area * 2 ** (d - c - 1) * gamma((d - c) / 2)
    Bc = Ic / gamma(1 + c / 2)
    cgt = 2 ** (-c) * gamma((d - c) / 2) / (gamma(mpf(d) / 2) * gamma(1 + c / 2))
    R = gamma((d - c) / 2) / (2 ** c * pi ** (mpf(d) / 2) * gamma(c / 2))
    print(f"  d = {d}, c = {nstr(c, 3)}: B_c = {nstr(Bc, 15)}   CGT constant at alpha = c: {nstr(cgt, 15)}   R(d,c)|S|/c = {nstr(R * area / c, 15)}")
    assert abs(Bc - cgt) < mpf(10) ** (-20) and abs(Bc - R * area / c) < mpf(10) ** (-20)

print("(14) the plane half of the example w = 4")
m, lam = mpf(3) / 2, mpf(1) / 2
h = lambda z: z ** m * (exp(-z) - lam * exp(-z / 2))
zstar = findroot(lambda z: diff(h, z), mpf("0.6"))
M2 = h(zstar)
w2 = gamma(m) / (2 * M2)
cone_bound = (2 * m) ** m * (1 - lam) ** (m + 1) / (m + 1) ** (m + 1)
print(f"  M_2 = sup z^(3/2)(e^(-z) - e^(-z/2)/2) = {nstr(M2, 12)} at z = {nstr(zstar, 8)};  w_2 = Gamma(3/2)/(2 M_2) = {nstr(w2, 10)}")
print(f"  the cone paper's bound on the supremum: 3^(3/2) 5^(-5/2) = {nstr(cone_bound, 12)} >= M_2;"
      f"  4 x it = {nstr(4 * cone_bound, 10)} <= Gamma(3/2)/2 = sqrt(pi)/4 = {nstr(sqrt(pi) / 4, 10)}"
      f"  (6912/3125 = {nstr(mpf(6912) / 3125, 8)} <= pi)")
assert M2 <= cone_bound and 4 * cone_bound <= sqrt(pi) / 4 and w2 >= 4
grid_max = max(h(mpf(j) / 1000) for j in range(1, 20001))
assert grid_max <= M2 + mpf(10) ** (-12)
print(f"  so 4 <= Gamma(3/2)/(2 x 3^(3/2) 5^(-5/2)) = {nstr(gamma(m) / (2 * cone_bound), 8)} <= w_2: proved in print, with no computed value")
# the same at d = 1 (c <= 6 + 4 sqrt 2), for the line half
m1, lam1 = mpf(1), 2 ** (-mpf(1) / 2)
cb1 = (2 * m1) ** m1 * (1 - lam1) ** (m1 + 1) / (m1 + 1) ** (m1 + 1)
print(f"  d = 1: the bound is (1 - 2^(-1/2))^2/2 = {nstr(cb1, 10)}, so the criterion holds for w <= Gamma(1)/(2 x it) = {nstr(1 / (2 * cb1), 10)} = 6 + 4 sqrt 2 = {nstr(6 + 4 * sqrt(2), 10)}")
print("all assertions passed")
