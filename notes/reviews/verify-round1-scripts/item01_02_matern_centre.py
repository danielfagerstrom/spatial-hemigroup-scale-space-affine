"""VERIFY round 1, items 1 and 2: the Matern kernel at its centre.

The Matern kernel of index g on R^d (paper-iso, eq:matern-density) has the radial density

    p_d(r) = 2 / ((2 pi)^(d/2) Gamma(g)) * (r / sqrt 2)^(g - d/2) * K_(g - d/2)(sqrt 2 r),

and c = 2 g in every dimension.

Item 1 (the sentence "The power cannot be improved" after prop:origin-lower-bound-d, which admits
every finite c > 0):
  (a) c > d (d = 2, g = 3/2, c = 3): the density is continuous with p(0) = (2 pi)^(-d/2)
      Gamma(g - d/2)/Gamma(g) > 0, so p(r) >= p(0)/2 near 0, a bound c_1 r^(beta - d) with
      beta = d < c. The quotient p(r) / r^(c - d) is unbounded as r -> 0: the power c - d is not sharp.
  (b) c <= d (d = 2, g = 3/4, c = 3/2): p(r) / r^(beta - d) -> 0 for beta < c, so no bound at a
      power beta < c holds, and p(r) / r^(c - d) has a positive finite limit.

Item 2 (the sentence "In Figure 1 the slopes at the centre are 2 gamma - d", g = 3/4, d = 1, 2, 3):
  the local slope d log p / d log r at small r is 2 g - d = -1/2, -3/2 for d = 2, 3, and 0 for
  d = 1, where 2 g - d = +1/2 and p_1(0) = (2 pi)^(-1/2) Gamma(1/4)/Gamma(3/4) = 1.18034...;
  p_1(0) - p_1(r) is of order r^(1/2).

Run: uv run --no-project --with mpmath python item01_02_matern_centre.py
"""
from mpmath import mp, mpf, besselk, gamma, pi, sqrt, log

mp.dps = 40


def p(r, d, g):
    nu = mpf(g) - mpf(d) / 2
    return 2 / ((2 * pi) ** (mpf(d) / 2) * gamma(g)) * (r / sqrt(2)) ** nu * besselk(nu, sqrt(2) * r)


def p0(d, g):
    return (2 * pi) ** (-mpf(d) / 2) * gamma(mpf(g) - mpf(d) / 2) / gamma(g)


print("Item 1(a): d = 2, gamma = 3/2, c = 3 > d")
d, g = 2, mpf(3) / 2
print("  p(0) =", mp.nstr(p0(d, g), 12))
for e in (1, 2, 3, 4, 6):
    r = mpf(10) ** (-e)
    print(f"  r = 1e-{e}: p(r)/p(0) = {mp.nstr(p(r, d, g) / p0(d, g), 10)},"
          f"  p(r)/r^(c-d) = {mp.nstr(p(r, d, g) / r ** (2 * g - d), 8)}")
    assert p(r, d, g) > p0(d, g) / 2
print("  so p >= p(0)/2 near 0 (beta = d < c), and p(r)/r^(c-d) is unbounded: the power c - d is not sharp")

print("Item 1(b): d = 2, gamma = 3/4, c = 3/2 <= d")
d, g = 2, mpf(3) / 4
c = 2 * g
limit = 2 ** (-g) * pi ** (-mpf(d) / 2) * gamma(mpf(d) / 2 - g) / gamma(g)
for beta in (c - mpf(1) / 4, c):
    print(f"  beta = {mp.nstr(beta, 4)}:")
    for e in (2, 4, 8, 16):
        r = mpf(10) ** (-e)
        print(f"    r = 1e-{e}: p(r)/r^(beta-d) = {mp.nstr(p(r, d, g) / r ** (beta - d), 10)}")
print("  limit of p(r)/r^(c-d):", mp.nstr(limit, 10), "(the constant of the paper, R(d, 2g) 2^g)")

print("Item 2: gamma = 3/4, local slope of log p_d against log r")
g = mpf(3) / 4
for d in (1, 2, 3):
    for e in (3, 6, 12):
        r1, r2 = mpf(10) ** (-e), mpf(10) ** (-e + 1)
        s = (log(p(r2, d, g)) - log(p(r1, d, g))) / (log(r2) - log(r1))
        print(f"  d = {d}, r in [1e-{e}, 1e-{e-1}]: slope = {mp.nstr(s, 8)}   (2 gamma - d = {mp.nstr(2*g-d, 3)})")
print("  p_1(0) =", mp.nstr(p0(1, g), 12))
for e in (2, 4, 6):
    r = mpf(10) ** (-e)
    print(f"  (p_1(0) - p_1(r)) / r^(1/2) at r = 1e-{e}: {mp.nstr((p0(1, g) - p(r, 1, g)) / sqrt(r), 10)}")
