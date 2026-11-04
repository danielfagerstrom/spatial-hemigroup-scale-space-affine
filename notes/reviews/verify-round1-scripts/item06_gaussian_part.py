"""VERIFY round 1, item 6(b): the Gaussian part in prop:isotropic-radial-monotone.

(1) The isotropic Gaussian N(0, a I) on R^d is a mixture of the uniform laws on the centred balls
    B_rho: with g_a its density and V_d the volume of the unit ball,

        g_a(x) = int_0^inf  1_{|x| < rho} / (V_d rho^d)  w(rho) d rho,
        w(rho) = V_d rho^(d+1) g_a(rho) / a  >= 0,   int_0^inf w = 1

    (the layer-cake formula; this is Kanter's Lemma 3.1, p. 70, for this law). Checked: the total
    mass of w, and the identity at several x.

(2) The volume of the intersection of two balls B(0, R) and B(x, R') is nonincreasing in |x|
    (closed forms for d = 1, 2, 3, on a grid of radii and distances). With the layer-cake formula
    for both factors this is the statement that the convolution of two radially nonincreasing
    functions is radially nonincreasing.

(3) The convolution of the Matern kernel of index 3/4 (unbounded at the centre for d = 2, 3) with
    N(0, a I): its radial density, by Fourier inversion of exp(-a rho^2/2) (1 + rho^2/2)^(-3/4), is
    decreasing in r on a grid (d = 2 and d = 3, a = 0.3).

Run: uv run --no-project --with mpmath python item06_gaussian_part.py
"""
from mpmath import mp, mpf, gamma, pi, sqrt, exp, quad, inf, besselj, sin, acos

mp.dps = 20


def V(d):
    return pi ** (mpf(d) / 2) / gamma(mpf(d) / 2 + 1)


def g(a, d, r):
    return (2 * pi * a) ** (-mpf(d) / 2) * exp(-r * r / (2 * a))


print("(1) the Gaussian as a mixture of uniform laws on centred balls")
for d in (1, 2, 3, 5):
    a = mpf("0.7")
    w = lambda rho: V(d) * rho ** (d + 1) * g(a, d, rho) / a
    total = quad(w, [0, 1, 5, inf])
    errs = []
    for x in (mpf("0.01"), mpf("0.5"), mpf(2)):
        mix = quad(lambda rho: w(rho) / (V(d) * rho ** d), [x, x + 1, x + 5, inf])
        errs.append(abs(mix - g(a, d, x)) / g(a, d, x))
    print(f"  d = {d}: int w = {mp.nstr(total, 15)}, largest relative error of the identity {mp.nstr(max(errs), 3)}")
    assert abs(total - 1) < mpf(10) ** (-12) and max(errs) < mpf(10) ** (-12)


def lens(d, R, Rp, t):
    """|B(0,R) cap B(t e, R')| in dimension d = 1, 2, 3."""
    if t >= R + Rp:
        return mpf(0)
    if t <= abs(R - Rp):
        return V(d) * min(R, Rp) ** d
    if d == 1:
        return min(R, t + Rp) - max(-R, t - Rp)
    if d == 2:
        a1 = R * R * acos((t * t + R * R - Rp * Rp) / (2 * t * R))
        a2 = Rp * Rp * acos((t * t + Rp * Rp - R * R) / (2 * t * Rp))
        a3 = sqrt((-t + R + Rp) * (t + R - Rp) * (t - R + Rp) * (t + R + Rp)) / 2
        return a1 + a2 - a3
    return pi * (R + Rp - t) ** 2 * (t * t + 2 * t * (R + Rp) - 3 * (R - Rp) ** 2) / (12 * t)


print("(2) the intersection of two balls is nonincreasing in the distance of the centres")
count = 0
for d in (1, 2, 3):
    for R in (mpf("0.3"), mpf(1), mpf("2.5")):
        for Rp in (mpf("0.2"), mpf(1), mpf(3)):
            prev = None
            for i in range(0, 601):
                v = lens(d, R, Rp, mpf(i) / 100)
                if prev is not None:
                    assert v <= prev + mpf(10) ** (-15), (d, R, Rp, i)
                    count += 1
                prev = v
print(f"  {count} consecutive pairs checked, d = 1, 2, 3")

print("(3) Matern(3/4) * N(0, a I), a = 0.3: the radial density is decreasing")
a, gam = mpf("0.3"), mpf(3) / 4
phi = lambda rho: exp(-a * rho * rho / 2) * (1 + rho * rho / 2) ** (-gam)
for d in (2, 3):
    vals = []
    for i in range(0, 41):
        r = mpf(i) / 8
        if d == 2:
            v = quad(lambda rho: rho * besselj(0, rho * r) * phi(rho), [0, 1, 4, 12, 30]) / (2 * pi)
        elif r == 0:
            v = quad(lambda rho: rho * rho * phi(rho), [0, 1, 4, 12, 30]) / (2 * pi ** 2)
        else:
            v = quad(lambda rho: rho * sin(rho * r) * phi(rho), [0, 1, 4, 12, 30]) / (2 * pi ** 2 * r)
        vals.append(v)
    assert all(vals[i + 1] < vals[i] for i in range(len(vals) - 1))
    print(f"  d = {d}: p(0) = {mp.nstr(vals[0], 8)}, p(1) = {mp.nstr(vals[8], 8)}, p(5) = {mp.nstr(vals[40], 8)};"
          f" decreasing on r = 0, 1/8, ..., 5")
