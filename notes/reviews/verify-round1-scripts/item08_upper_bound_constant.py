"""VERIFY round 1, item 8: the constant of prop:origin-upper-bound-d, explicit in the datum.

The proofs (paper-iso, appendix: Theorem thm:origin-boundedness-d, clauses (1) and (4), and
Proposition prop:origin-upper-bound-d, clause (1)) give, for 0 < beta < c <= d:

  beta_1 in (beta, c);  r_beta in (0, 1] with k_d(r_beta) >= beta_1;
  eps in (0, 1] with  sigma{|eta_1| >= eps}/|S^(d-1)| >= beta/beta_1;
  L = 3 - log(eps r_beta);   C_beta = 2^beta (1 + e^(beta L));
  C'_beta = (2 pi)^(-d) C_beta |S^(d-1)| 2^((d-beta)/2 - 1) Gamma((d-beta)/2)     [the referee's formula]
  A_beta = (2 pi)^(d/2) e^(1/2) C'_beta.

A choice that is explicit: beta_1 = (beta + c)/2, eps = (c - beta)/((c + beta) sqrt d). Then

  A_beta = sqrt(e) 2^(beta/2) Gamma((d-beta)/2)/Gamma(d/2)
           * (1 + (e^3 sqrt(d) (c + beta) / ((c - beta) r_beta))^beta).

This script checks
  (1) the Gaussian integral  int |y|^(-beta) e^(-|y|^2/2) dy = |S^(d-1)| 2^((d-beta)/2-1) Gamma((d-beta)/2);
  (2) the cap estimate behind the choice of eps: the normalized measure of the band
      {|eta_1| < eps} on S^(d-1) is at most eps sqrt(d), for d = 1..12;
  (3) that the closed form of A_beta equals (2 pi)^(d/2) e^(1/2) C'_beta;
  (4) on Matern kernels with c = 2 gamma <= d, each inequality of the chain with these constants:
      muhat <= C_beta (1 + rho)^(-beta);  int g_t dmu <= C'_beta t^(-(d-beta)/2);
      mu(B_r) <= A_beta r^beta;  q(r) <= A_beta r^(beta-d)/V_d.

Run: uv run --no-project --with mpmath python item08_upper_bound_constant.py
"""
from mpmath import (mp, mpf, besselk, gamma, pi, sqrt, log, exp, quad, inf, betainc, findroot)

mp.dps = 25


def sphere(d):
    return 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)


def ball(d):
    return pi ** (mpf(d) / 2) / gamma(mpf(d) / 2 + 1)


print("(1) the Gaussian integral")
for d, beta in ((1, mpf(1) / 4), (2, mpf(1)), (3, mpf(3) / 2), (5, mpf(4))):
    lhs = sphere(d) * quad(lambda r: r ** (d - 1 - beta) * exp(-r * r / 2), [0, 1, inf])
    rhs = sphere(d) * 2 ** ((d - beta) / 2 - 1) * gamma((d - beta) / 2)
    print(f"  d = {d}, beta = {mp.nstr(beta, 4)}: {mp.nstr(lhs, 15)}  {mp.nstr(rhs, 15)}")
    assert abs(lhs - rhs) < mpf(10) ** (-15) * rhs

print("(2) the band {|eta_1| < eps} has normalized measure <= eps sqrt(d)")
worst = mpf(0)
for d in range(1, 13):
    for k in range(1, 100):
        eps = mpf(k) / 100
        if d == 1:
            band = mpf(0)                      # S^0 = {+1, -1}: |eta_1| = 1 > eps
        else:
            band = betainc(mpf(1) / 2, mpf(d - 1) / 2, 0, eps * eps, regularized=True)
        worst = max(worst, band / (eps * sqrt(d)))
        assert band <= eps * sqrt(d)
print("  largest band/(eps sqrt d) over d = 1..12, eps = 0.01..0.99:", mp.nstr(worst, 6))


def constants(d, c, beta, r_beta):
    beta1 = (beta + c) / 2
    eps = (c - beta) / ((c + beta) * sqrt(d))
    L = 3 - log(eps * r_beta)
    C = 2 ** beta * (1 + exp(beta * L))
    Cp = (2 * pi) ** (-d) * C * sphere(d) * 2 ** ((d - beta) / 2 - 1) * gamma((d - beta) / 2)
    A = (2 * pi) ** (mpf(d) / 2) * exp(mpf(1) / 2) * Cp
    A_closed = (sqrt(exp(1)) * 2 ** (beta / 2) * gamma((d - beta) / 2) / gamma(mpf(d) / 2)
                * (1 + (exp(3) * sqrt(d) * (c + beta) / ((c - beta) * r_beta)) ** beta))
    return beta1, eps, L, C, Cp, A, A_closed


print("(3), (4) Matern kernels")
for d, g, beta in ((1, mpf(1) / 4, mpf(1) / 4), (2, mpf(3) / 4, mpf(1)), (2, mpf(1), mpf(3) / 2),
                   (3, mpf(1), mpf(3) / 2), (3, mpf(3) / 2, mpf(2))):
    c = 2 * g
    k = lambda r: 2 * g / gamma(mpf(d) / 2) * 2 * (r * r / 2) ** (mpf(d) / 4) * besselk(mpf(d) / 2, sqrt(2) * r)
    beta1 = (beta + c) / 2
    r_beta = min(mpf(1), findroot(lambda r: k(r) - beta1, mpf("0.1")))
    assert k(r_beta) >= beta1 - mpf(10) ** (-15) and 0 < r_beta <= 1
    beta1, eps, L, C, Cp, A, A_closed = constants(d, c, beta, r_beta)
    assert abs(A - A_closed) < mpf(10) ** (-15) * A
    muhat = lambda rho: (1 + rho * rho / 2) ** (-g)
    dens = lambda r: (2 / ((2 * pi) ** (mpf(d) / 2) * gamma(g)) * (r / sqrt(2)) ** (g - mpf(d) / 2)
                      * besselk(g - mpf(d) / 2, sqrt(2) * r))
    w1 = max(muhat(rho) / (C * (1 + rho) ** (-beta)) for rho in [mpf(10) ** (e / 4) for e in range(-12, 41)])
    w2 = mpf(0)
    for e in range(-16, 9):
        t = mpf(10) ** (mpf(e) / 2)
        val = (2 * pi) ** (-d) * sphere(d) * quad(
            lambda rho: rho ** (d - 1) * muhat(rho) * exp(-t * rho * rho / 2), [0, 1, 1 / sqrt(t), inf])
        w2 = max(w2, val / (Cp * t ** (-(d - beta) / 2)))
    w3 = w4 = mpf(0)
    for e in range(-12, 5):
        r = mpf(10) ** (mpf(e) / 2)
        mass = sphere(d) * quad(lambda s: s ** (d - 1) * dens(s), [0, r / 2, r])
        w3 = max(w3, mass / (A * r ** beta))
        w4 = max(w4, dens(r) / (A / ball(d) * r ** (beta - d)))
    print(f"  d = {d}, gamma = {mp.nstr(g, 3)}, c = {mp.nstr(c, 3)}, beta = {mp.nstr(beta, 3)}: "
          f"r_beta = {mp.nstr(r_beta, 5)}, C_beta = {mp.nstr(C, 5)}, C'_beta = {mp.nstr(Cp, 5)}, "
          f"A_beta = {mp.nstr(A, 5)}")
    print(f"     largest quotient lhs/rhs:  transform {mp.nstr(w1, 4)};  blurred centre {mp.nstr(w2, 4)};"
          f"  ball {mp.nstr(w3, 4)};  density {mp.nstr(w4, 4)}")
    assert max(w1, w2, w3, w4) <= 1
print("all inequalities hold with the explicit constants")
