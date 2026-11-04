"""VERIFY round 1, item 9: the shadow in R^d of an isotropic Levy measure on R^(d+1).

Let nu' on R^(d+1) have the density k'(|z|) / (|S^d| |z|^(d+1)), k' >= 0 nonincreasing, and let
nubar be its image under the projection on the first d coordinates. Integrating over the last
coordinate h = r u, the polar profile of nubar in dimension d is

    kbar(r) = C_d * int_R k'(r sqrt(1 + u^2)) (1 + u^2)^(-(d+1)/2) du,
    C_d = |S^(d-1)| / |S^d| = Gamma((d+1)/2) / (sqrt(pi) Gamma(d/2)),

and C_d * int_R (1 + u^2)^(-(d+1)/2) du = 1.

Checks:
  (1) the normalization, d = 1..8;
  (2) the formula on the Matern exponent gamma log(1 + r^2/2), whose polar profile in dimension d
      is k_d(r) = (4 gamma / Gamma(d/2)) (r^2/2)^(d/4) K_(d/2)(sqrt 2 r) (eq:polar-profile-d with
      k_I = gamma e^(-u)): the shadow of the datum in dimension d+1 is the datum in dimension d;
  (3) the shadow of a step k' = b 1_(0,tau) in dimension d+1: kbar is continuous, kbar(0+) = b,
      and kbar(r) -> 0 as r -> tau, like a multiple of sqrt(1 - r/tau). So no nonincreasing k'
      vanishing beyond tau, which is bounded on [tau/2, tau] by k'(tau/2), has the step
      b 1_(0,tau) as its shadow: the shadow's profile on [tau/2, tau) is at most
      2 C_d k'(tau/2) sqrt(tau^2/r^2 - 1), which tends to 0, and the step's is b.

Run: uv run --no-project --with mpmath python item09_projection_of_polar_profile.py
"""
from mpmath import mp, mpf, besselk, gamma, pi, sqrt, quad, inf

mp.dps = 25


def C(d):
    return gamma(mpf(d + 1) / 2) / (sqrt(pi) * gamma(mpf(d) / 2))


def shadow(kp, d, r, umax=inf):
    pts = [0, 1, 10, umax] if umax == inf else [0, umax]
    return C(d) * 2 * quad(lambda u: kp(r * sqrt(1 + u * u)) * (1 + u * u) ** (-mpf(d + 1) / 2), pts)


print("(1) C_d int_R (1+u^2)^(-(d+1)/2) du")
for d in range(1, 9):
    v = C(d) * 2 * quad(lambda u: (1 + u * u) ** (-mpf(d + 1) / 2), [0, 1, 10, inf])
    print(f"  d = {d}: {mp.nstr(v, 15)}")
    assert abs(v - 1) < mpf(10) ** (-12)


def k_matern(d, g):
    return lambda r: 4 * g / gamma(mpf(d) / 2) * (r * r / 2) ** (mpf(d) / 4) * besselk(mpf(d) / 2, sqrt(2) * r)


print("(2) Matern: the shadow of the datum in dimension d+1 against the datum in dimension d")
g = mpf(3) / 4
for d in (1, 2, 3, 4):
    for r in (mpf("0.05"), mpf("0.5"), mpf(2)):
        a, b = shadow(k_matern(d + 1, g), d, r), k_matern(d, g)(r)
        print(f"  d = {d}, r = {mp.nstr(r, 3)}: shadow {mp.nstr(a, 12)}   k_d {mp.nstr(b, 12)}")
        assert abs(a - b) < mpf(10) ** (-10) * b

print("(3) the shadow of the step b 1_(0,tau), b = tau = 1, from dimension d+1")
for d in (1, 2, 3):
    row = []
    for r in (mpf("0.001"), mpf("0.5"), mpf("0.9"), mpf("0.99"), mpf("0.9999")):
        um = sqrt(1 / (r * r) - 1)
        v = C(d) * 2 * quad(lambda u: (1 + u * u) ** (-mpf(d + 1) / 2), [0, um])
        row.append(f"kbar({mp.nstr(r, 4)}) = {mp.nstr(v, 6)}")
        bound = 2 * C(d) * um
        assert v <= bound
    r = mpf("0.9999")
    um = sqrt(1 / (r * r) - 1)
    v = C(d) * 2 * quad(lambda u: (1 + u * u) ** (-mpf(d + 1) / 2), [0, um])
    print(f"  d = {d}: " + ", ".join(row) + f";  kbar/sqrt(1-r) at 0.9999 = {mp.nstr(v / sqrt(1 - r), 6)}"
          f"  (2 sqrt 2 C_d = {mp.nstr(2 * sqrt(2) * C(d), 6)})")
