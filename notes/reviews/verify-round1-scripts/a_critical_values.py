"""Q-0423, review round 1 of the isotropic paper, required change 6: does sqrt(d) w_d have a limit?

The critical values of def:filtration-thresholds (eq:threshold-constant), for a real d >= 1:

    m = (d+1)/2,   h_d(z) = z^m (e^{-z} - 2^{-d/2} e^{-z/2}),   M_d = sup_{z>0} h_d(z),
    w_d = Gamma(m) / (2 M_d).

lem:threshold-limit (Lemma A.5 of the paper) proves, with eps_d = 2^{-d/2} e^{m/2},

    m^m e^{-m} (1 - eps_d) <= M_d <= m^m e^{-m},        eps_d -> 0,

and the two-sided Stirling bound e^{-1/2} <= sqrt(m) I_m <= K, where
I_m = Gamma(m) m^{-m} e^{m} = int_{-1}^infty e^{-m(u - log(1+u))} du.

The claim checked here: sqrt(m) I_m -> sqrt(2 pi) (Stirling's formula), hence

    sqrt(m) w_d -> sqrt(pi/2)   and   sqrt(d) w_d -> sqrt(pi) = 1.7724538509...

What the script does.
 1. Computes M_d by solving the first-order condition m(1-q) = z(1 - q/2), q = 2^{-d/2} e^{z/2}
    (proof of lem:threshold-monotone) on (0, d log 2), after locating the maximum of log h_d on a
    grid; it reports the number of sign changes of the first-order function on the grid (one
    means a single interior critical point).
 2. Tabulates w_d, sqrt(d) w_d, its relative distance to sqrt(pi), that distance times d (the
    expansion below predicts -1/3), and the squeeze of the proof:
        sqrt(d/m) sqrt(m) I_m / 2  <=  sqrt(d) w_d  <=  sqrt(d/m) sqrt(m) I_m / (2 (1 - eps_d)).
 3. Checks the three values the referee quotes (w_1, w_2, w_3) and the monotonicity of w_d.

Expansion (not claimed in the record beyond its first term): Gamma(m) = sqrt(2 pi) m^{m-1/2}
e^{-m} (1 + 1/(12 m) + O(m^-2)) and M_d = m^m e^{-m} (1 - O(eps_d)) give
sqrt(d) w_d = sqrt(pi) (1 - 1/(3d) + O(d^-2)) + O(eps_d).

Run from the repository root:
    uv run --no-project --with mpmath python \
        records/affine/reviews/verify-round1-scripts/a_critical_values.py \
        > records/affine/reviews/verify-round1-scripts/a_critical_values-output.txt
"""
from mpmath import mp, mpf, exp, log, sqrt, pi, findroot, loggamma, linspace

mp.dps = 40


def log_h(d, z):
    """log h_d(z) on (0, d log 2)."""
    m = (d + 1) / 2
    return m * log(z) - z + log(1 - mpf(2) ** (-d / 2) * exp(z / 2))


def first_order(d, z):
    """m(1 - q) - z(1 - q/2), q = 2^{-d/2} e^{z/2}: a positive multiple of h_d'(z)."""
    m = (d + 1) / 2
    q = mpf(2) ** (-d / 2) * exp(z / 2)
    return m * (1 - q) - z * (1 - q / 2)


def threshold(d, grid=4001):
    """(w_d, log M_d, z*, q*, number of sign changes of the first-order function on the grid)."""
    d = mpf(d)
    m = (d + 1) / 2
    top = d * log(2)
    zs = [top * mpf(j) / grid for j in range(1, grid)]
    fo = [first_order(d, z) for z in zs]
    changes = sum(1 for a, b in zip(fo, fo[1:]) if (a > 0) != (b > 0))
    best = max(zs, key=lambda z: log_h(d, z))
    step = top / grid
    zstar = findroot(lambda z: first_order(d, z), (best - step, best + step), solver="anderson")
    if not (0 < zstar < top):
        raise RuntimeError(f"maximiser left (0, d log 2) at d = {d}")
    lM = log_h(d, zstar)
    if lM < log_h(d, best) - mpf(10) ** (-30):
        raise RuntimeError(f"root is not the grid maximum at d = {d}")
    q = mpf(2) ** (-d / 2) * exp(zstar / 2)
    w = exp(loggamma(m) - log(2) - lM)
    return w, lM, zstar, q, changes


def stirling_ratio(m):
    """sqrt(m) I_m = Gamma(m) m^{1/2 - m} e^{m}."""
    return exp(loggamma(m) + (mpf(1) / 2 - m) * log(m) + m)


def main():
    rp = sqrt(pi)
    print("Critical values w_d = Gamma(m)/(2 M_d), m = (d+1)/2 (def:filtration-thresholds)")
    print(f"sqrt(pi)    = {mp.nstr(rp, 15)}")
    print(f"sqrt(pi/2)  = {mp.nstr(sqrt(pi / 2), 15)}")
    print(f"sqrt(2 pi)  = {mp.nstr(sqrt(2 * pi), 15)}")
    print()

    ds = [1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40, 50, 60, 80, 100, 200, 500, 1000, 2000, 5000]
    rows = []
    hdr = (f"{'d':>5} {'z*/m':>10} {'q*':>10} {'eps_d':>10} {'w_d':>14} {'sqrt(d) w_d':>13} "
           f"{'rel. dist.':>11} {'d * rel.':>9} {'squeeze low':>12} {'squeeze up':>12} {'sc':>3}")
    print(hdr)
    for d in ds:
        w, lM, z, q, ch = threshold(d)
        dm = mpf(d)
        m = (dm + 1) / 2
        eps = mpf(2) ** (-dm / 2) * exp(m / 2)
        s = sqrt(dm) * w
        rel = s / rp - 1
        lo = sqrt(dm / m) * stirling_ratio(m) / 2
        up = lo / (1 - eps) if eps < 1 else mpf("inf")
        rows.append((d, w, s, lo, up, eps, lM, m))
        ups = mp.nstr(up, 9) if eps < 1 else "inf"
        print(f"{d:5d} {mp.nstr(z / m, 8):>10} {mp.nstr(q, 4):>10} {mp.nstr(eps, 4):>10} "
              f"{mp.nstr(w, 10):>14} {mp.nstr(s, 10):>13} {mp.nstr(rel, 4):>11} "
              f"{mp.nstr(dm * rel, 5):>9} {mp.nstr(lo, 9):>12} {ups:>12} {ch:3d}")

    print()
    print("Stirling's ratio sqrt(m) I_m = Gamma(m) m^(1/2-m) e^m against sqrt(2 pi), and the")
    print("normalisation by m: sqrt(m) w_d against sqrt(pi/2):")
    print(f"{'d':>5} {'m':>7} {'sqrt(m) I_m / sqrt(2pi)':>24} {'sqrt(m) w_d':>13} "
          f"{'sqrt(m) w_d / sqrt(pi/2)':>25}")
    for d, w, s, lo, up, eps, lM, m in rows:
        print(f"{d:5d} {mp.nstr(m, 6):>7} {mp.nstr(stirling_ratio(m) / sqrt(2 * pi), 12):>24} "
              f"{mp.nstr(sqrt(m) * w, 10):>13} {mp.nstr(sqrt(m) * w / sqrt(pi / 2), 12):>25}")

    print()
    print("Checks (all must read True):")
    w1, w2, w3 = rows[0][1], rows[1][1], rows[2][1]
    print(f"  the referee's w_1 = 12.606252, w_2 = 5.242276, w_3 = 3.205618 reproduced to 6 "
          f"decimals: {[mp.nstr(x, 8) for x in (w1, w2, w3)]} -> "
          f"{all(abs(a - mpf(b)) < mpf('5e-7') for a, b in ((w1, '12.606252'), (w2, '5.242276'), (w3, '3.205618')))}")
    ws = [r[1] for r in rows]
    print(f"  w_d strictly decreasing along the table (lem:threshold-monotone): "
          f"{all(a > b for a, b in zip(ws, ws[1:]))}")
    print(f"  M_d <= m^m e^-m, and M_d >= m^m e^-m (1 - eps_d) where eps_d < 1 (lem:threshold-limit): "
          f"{all(r[6] <= r[7] * log(r[7]) - r[7] + mpf(10) ** (-30) and (r[5] >= 1 or r[6] >= r[7] * log(r[7]) - r[7] + log(1 - r[5]) - mpf(10) ** (-30)) for r in rows)}")
    print(f"  squeeze low <= sqrt(d) w_d <= squeeze up at every d of the table: "
          f"{all(r[3] <= r[2] * (1 + mpf(10) ** (-30)) and r[2] <= r[4] * (1 + mpf(10) ** (-30)) for r in rows)}")
    big = [r for r in rows if r[0] >= 1000]
    print(f"  |sqrt(d) w_d / sqrt(pi) - 1| < 1/(2d) for d >= 1000: "
          f"{all(abs(r[2] / rp - 1) < mpf(1) / (2 * r[0]) for r in big)}")
    print(f"  d (sqrt(d) w_d / sqrt(pi) - 1) within 0.002 of -1/3 for d >= 1000: "
          f"{all(abs(r[0] * (r[2] / rp - 1) + mpf(1) / 3) < mpf('0.002') for r in big)}")

    print()
    print("Where sqrt(d) w_d crosses sqrt(pi) (it decreases from 12.6, passes below sqrt(pi), and")
    print("returns to it from below): integers d = 30..140, the sign of sqrt(d) w_d - sqrt(pi):")
    prev = None
    smin = None
    for d in range(30, 141):
        w = threshold(d, grid=801)[0]
        s = sqrt(mpf(d)) * w
        if smin is None or s < smin[1]:
            smin = (d, s)
        sign = s > rp
        if prev is not None and sign != prev:
            print(f"  sign change between d = {d - 1} and d = {d}: sqrt({d}) w_{d} = {mp.nstr(s, 12)}")
        prev = sign
    print(f"  least value of sqrt(d) w_d over integers 30..140: d = {smin[0]}, {mp.nstr(smin[1], 12)}")


if __name__ == "__main__":
    main()
