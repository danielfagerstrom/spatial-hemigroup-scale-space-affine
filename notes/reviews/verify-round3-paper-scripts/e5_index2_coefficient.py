# /// script
# dependencies = ["numpy"]
# ///
"""Round 3, report D, item 3: the log-rate of the negative mass of the Matern increment at index 2.

Referee D claims that the coefficient of log(1/a) in the negative mass of the continuum increment of
the Matern orbit of index gamma, for the step t^2 I -> t^2 diag(1+eps, 1) in the plane, is computable
at every index from the degree-0 limit of the increment's transform,

    h(phi) = (<w, S w> / <w, S' w>)^gamma = ((1+eps) cos^2 phi + sin^2 phi)^(-gamma),

as the negative part of the angular factor A of the inverse transform of h - mean(h), a kernel
A(theta)/|x|^2. In R^2 the inverse transform (rho(x) = (2 pi)^-2 int rhohat(w) e^{-i<w,x>} dw) of
cos(2m phi) is (-1)^m (m/pi) cos(2m theta)/|x|^2 (Stein, Singular Integrals, ch. III, sec. 3.3,
Thm. 5: the transform of P_k(x)/|x|^{k+d} is gamma_k P_k(w)/|w|^k, gamma_k = i^{-k} pi^{d/2}
Gamma(k/2)/Gamma((k+d)/2); for d = 2, k = 2m this is (-1)^m pi/m). The negative mass on the shell
a < |x| < 1 is then log(1/a) * int_0^{2 pi} A_-(theta) d theta.

Checks:
 (1) gamma = 1 must give eps/(pi(1+eps)), Proposition E.4(4) of the paper (proved there by a
     different route). This checks the Fourier constant and the sign.
 (2) gamma = 2: the referee's values 0.00627, 0.05526, 0.17771.
 (3) the grid of Remark E.5 (the deposited script's construction, n = 64 t, natural log, ordinary
     least squares over t in {4, 8, 16, 32}), and a second fit over {8, 16, 32, 64}, to see whether
     the slope settles on the continuum rate as t grows.
 (4) a direct check of the angular factor at index 2 independent of the Fourier-series constant:
     the grid increment at t = 64 sampled on a circle of radius r (in grid units, t << r << n/2 is
     not available, so r between 2 and 6 t is used), times r^2, against A(theta).

Run: python3 records/affine/reviews/verify-round3-paper-scripts/e5_index2_coefficient.py
"""
import numpy as np


def h_coeffs(eps, gamma, M=400, N=8192):
    phi = 2 * np.pi * np.arange(N) / N
    h = ((1 + eps) * np.cos(phi) ** 2 + np.sin(phi) ** 2) ** (-gamma)
    # h is even and pi-periodic: h = a0 + sum a_m cos(2 m phi)
    a = np.array([2 * np.mean(h * np.cos(2 * m * phi)) for m in range(1, M + 1)])
    return np.mean(h), a


def angular_factor(eps, gamma, theta, M=400):
    a0, a = h_coeffs(eps, gamma, M)
    m = np.arange(1, M + 1)
    return ((a * (-1.0) ** m * m / np.pi)[None, :] * np.cos(2 * np.outer(theta, m))).sum(axis=1), a0


def continuum_rate(eps, gamma):
    theta = 2 * np.pi * np.arange(20000) / 20000
    A, a0 = angular_factor(eps, gamma, theta)
    return np.mean(np.maximum(-A, 0)) * 2 * np.pi, np.mean(np.maximum(A, 0)) * 2 * np.pi, a0


def symbol(S, T1, T2):
    s12 = S[0, 1]
    a, c = S[0, 0] - abs(s12), S[1, 1] - abs(s12)
    bp, bm = max(s12, 0.0), max(-s12, 0.0)
    return (a * (2 - 2 * np.cos(T1)) + c * (2 - 2 * np.cos(T2))
            + bp * (2 - 2 * np.cos(T1 + T2)) + bm * (2 - 2 * np.cos(T1 - T2)))


def grid_increment(t, eps, gamma):
    n = int(64 * t)
    th = 2 * np.pi * np.fft.fftfreq(n)
    T1, T2 = np.meshgrid(th, th, indexing="ij")
    S, S2 = t**2 * np.eye(2), t**2 * np.diag([1.0 + eps, 1.0])
    rhohat = ((1 + symbol(S, T1, T2)) / (1 + symbol(S2, T1, T2))) ** gamma
    return np.real(np.fft.ifft2(rhohat))


def main():
    print("(1),(2) continuum log-rate of the negative mass, int A_- d theta")
    print("  gamma   eps    rate(neg)   rate(pos)   eps/(pi(1+eps))   gamma*eps/(pi(1+eps))   mean h (atom)")
    for gamma in [1, 2]:
        for eps in [0.01, 0.1, 0.5]:
            neg, pos, a0 = continuum_rate(eps, gamma)
            print(f"  {gamma:5d}  {eps:4.2f}   {neg:.5f}     {pos:.5f}     {eps/(np.pi*(1+eps)):.5f}"
                  f"           {gamma*eps/(np.pi*(1+eps)):.5f}               {a0:.5f}")

    print("\n(3) grid slopes of the negative mass against ln t (OLS), Remark E.5's construction")
    for gamma in [1, 2]:
        for eps in [0.01, 0.1, 0.5]:
            masses = {}
            for t in [4, 8, 16, 32, 64]:
                rho = grid_increment(t, eps, gamma)
                masses[t] = -rho[rho < 0].sum()
            s1 = np.polyfit(np.log([4, 8, 16, 32]), [masses[t] for t in [4, 8, 16, 32]], 1)[0]
            s2 = np.polyfit(np.log([8, 16, 32, 64]), [masses[t] for t in [8, 16, 32, 64]], 1)[0]
            steps = [(masses[2 * t] - masses[t]) / np.log(2) for t in [4, 8, 16, 32]]
            neg, _, _ = continuum_rate(eps, gamma)
            print(f"  gamma {gamma}, eps {eps:4.2f}: slope 4-32 {s1:.4f}, slope 8-64 {s2:.4f}, "
                  f"per-doubling {', '.join(f'{s:.4f}' for s in steps)}; continuum {neg:.4f}; "
                  f"grid/continuum (4-32) {s1/neg:.3f}")

    print("\n(4) angular factor at index 2, eps = 0.5: r^2 * grid increment on circles, against A(theta)")
    t, eps, gamma = 64, 0.5, 2
    rho = grid_increment(t, eps, gamma)
    n = rho.shape[0]
    thetas = np.array([0, np.pi / 8, np.pi / 4, 3 * np.pi / 8, np.pi / 2])
    A, _ = angular_factor(eps, gamma, thetas)
    for r in [2 * t, 4 * t]:
        vals = []
        for th in thetas:
            # bilinear interpolation on the torus
            x, y = r * np.cos(th), r * np.sin(th)
            i0, j0 = int(np.floor(x)), int(np.floor(y))
            fx, fy = x - i0, y - j0
            v = ((1 - fx) * (1 - fy) * rho[i0 % n, j0 % n] + fx * (1 - fy) * rho[(i0 + 1) % n, j0 % n]
                 + (1 - fx) * fy * rho[i0 % n, (j0 + 1) % n] + fx * fy * rho[(i0 + 1) % n, (j0 + 1) % n])
            vals.append(v * r**2)
        print(f"  r = {r:4d}: r^2 rho = {', '.join(f'{v:+.4f}' for v in vals)}")
    print(f"  A(theta)  = {', '.join(f'{v:+.4f}' for v in A)}   (theta = 0, pi/8, pi/4, 3pi/8, pi/2)")
    print("  (the |x|^-2 term dominates only for r << t; at r ~ t the Matern tail e^{-r/t} and the")
    print("   lower-order terms are of the same size, so this is a rough check of sign and shape only)")
    for r in [4, 8, 16]:
        vals = []
        for th in thetas:
            x, y = r * np.cos(th), r * np.sin(th)
            i0, j0 = int(np.floor(x)), int(np.floor(y))
            fx, fy = x - i0, y - j0
            v = ((1 - fx) * (1 - fy) * rho[i0 % n, j0 % n] + fx * (1 - fy) * rho[(i0 + 1) % n, j0 % n]
                 + (1 - fx) * fy * rho[i0 % n, (j0 + 1) % n] + fx * fy * rho[(i0 + 1) % n, (j0 + 1) % n])
            vals.append(v * r**2)
        print(f"  r = {r:4d} (grid units, t = 64): r^2 rho = {', '.join(f'{v:+.4f}' for v in vals)}")


if __name__ == "__main__":
    main()
