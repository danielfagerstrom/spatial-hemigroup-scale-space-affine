"""Q-0423, review round 1 of the isotropic paper, required change 7, the boundary case c = d.

prop:origin-rate-d(2): at c = d, q(s) ~ (2 pi)^{-d} I(s), I(s) = int_{|xi| <= 1/s} mu-hat(xi) d xi
= |S^{d-1}| int_0^{1/s} mu-hat(rho e) rho^{d-1} d rho. With mu-hat(rho e) rho^d = L(rho) ~
A(d,d,C_k) K(1/rho) (b_slowly_varying_factor.py) and K >= 1, the integral diverges and

    I(s) ~ |S^{d-1}| A(d,d,C_k) int_s^1 K(y) dy/y,

so that q(s) ~ B(d, C_k) Lcal(s), with

    Lcal(s) = int_s^1 K(y) dy/y            (Sato's L of (53.26), Sato-Yamazato's (1.10)),
    B(d, C_k) = (2 pi)^{-d} |S^{d-1}| A(d,d,C_k)
              = 2 exp(-C_k - (d/2)(gamma_E - psi(d/2))) / (pi^{d/2} Gamma(d/2)).

At d = 1, B = e^{-gamma_E - C_k}/pi, the constant kappa/pi of Sato's (53.30) for a symmetric law.

Checked here on the Matern kernel of index gamma = d/2 (c = d), whose density is
p(x) = 2 K_0(sqrt 2 |x|) / ((2 pi)^{d/2} Gamma(d/2)) (eq:matern-density): the quotient
p / (B Lcal) tends to 1 at the rate 1/log(1/s), and the difference p - B Lcal stays bounded (it
tends to a constant), which is the sharper form of the same check.

Run from the repository root:
    uv run --no-project --with mpmath python \
        records/affine/reviews/verify-round1-scripts/c_critical_case.py \
        > records/affine/reviews/verify-round1-scripts/c_critical_case-output.txt
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from mpmath import digamma, euler, exp, gamma, log, mp, mpf, pi, quad  # noqa: E402

import b_slowly_varying_factor as B  # noqa: E402


def main():
    mp.dps = 20
    print("The boundary case c = d on the Matern kernel of index gamma = d/2 (20 digits).")
    for d in (1, 2, 3):
        gam = mpf(d) / 2
        c = 2 * gam
        Ck = B.matern_Ck(d, gam)
        A = B.A_const(d, c, Ck)
        area = 2 * pi ** (mpf(d) / 2) / gamma(mpf(d) / 2)
        Bc = (2 * pi) ** (-d) * area * A
        Bc2 = 2 * exp(-Ck - mpf(d) / 2 * (euler - digamma(mpf(d) / 2))) / (pi ** (mpf(d) / 2) * gamma(mpf(d) / 2))
        assert abs(Bc / Bc2 - 1) < mpf(10) ** (-17)
        K0 = exp(B.matern_logK0(d, gam))
        print(f"  d = {d}: C_k = {mp.nstr(Ck, 12)}, A = {mp.nstr(A, 12)}, B = {mp.nstr(Bc, 12)}, "
              f"K(0+) = {mp.nstr(K0, 12)}, B K(0+) = {mp.nstr(Bc * K0, 12)}, "
              f"2 (2 pi)^(-d/2)/Gamma(d/2) = {mp.nstr(2 * (2 * pi) ** (-mpf(d) / 2) / gamma(mpf(d) / 2), 12)}")
        print(f"    {'s':>7} {'p(s)':>16} {'B Lcal(s)':>16} {'quotient':>14} {'difference':>14}")
        # Lcal(s) = int_s^1 K(y) dy/y, accumulated decade by decade; inside a decade [lo, hi],
        # log K(y) = log K(hi) + int_y^hi (c - k_d(u)) du/u
        acc = mpf(0)
        hi = mpf(1)
        base = mpf(0)
        integrand = lambda u: (c - B.matern_k(d, gam, u)) / u
        for e in range(1, 11):
            lo = mpf(10) ** (-e)
            acc += quad(lambda y: exp(base + quad(integrand, [y, hi])) / y, [lo, hi])
            base += quad(integrand, [lo, hi])
            hi = lo
            if e in (1, 2, 3, 4, 6, 8, 10):
                p = B.matern_density(d, gam, lo)
                print(f"    {'1e-' + str(e):>7} {mp.nstr(p, 10):>16} {mp.nstr(Bc * acc, 10):>16} "
                      f"{mp.nstr(p / (Bc * acc), 8):>14} {mp.nstr(p - Bc * acc, 8):>14}")
            sys.stdout.flush()
    print()


if __name__ == "__main__":
    main()
