# /// script
# dependencies = ["numpy"]
# ///
"""Does the discrete Matern (Helmholtz) family on the grid cascade across small shape changes?

In the continuum, the Matern orbit of every index has no positive increment off the rays
(prop:matern-steps): the increment's transform tends to a nonconstant function of the direction at
infinite frequency, and its negative part has infinite mass at the origin. On the lattice Z^2
frequencies are bounded, so that argument does not apply. This script measures how negative the
lattice increment is.

The anisotropic lattice operator is the generator of a random walk with jumps +-e1, +-e2,
+-(e1+e2), +-(e1-e2):

    D_S(th) = a (2 - 2cos th1) + c (2 - 2cos th2) + bp (2 - 2cos(th1+th2)) + bm (2 - 2cos(th1-th2)),

with a = S11 - |S12|, c = S22 - |S12|, bp = max(S12, 0), bm = max(-S12, 0), so that
D_S(th) = th' S th + O(|th|^4); it needs S diagonally dominant. (1 + D_S)^(-gamma) is a positive
lattice kernel (the resolvent of a random walk). The increment of the step S -> S' has transform

    rho^(th) = ((1 + D_S(th)) / (1 + D_S'(th)))^gamma,

computed on an n x n torus by FFT. Calibration: a ray step S' = lam^2 S has D_S' = lam^2 D_S, and the
increment is a positive measure exactly, so its computed negative mass is the numerical floor.

The last block computes the coefficient that the slopes are compared with at every index (round 3 of
the external review, report D; records/affine/reviews/VERIFY-round3-landscape-orbits-paper.md,
item 5, whose verification script e5_index2_coefficient.py it ports): the negative-mass rate of the
|x|^-2 term of the continuum increment, read off the degree-0 limit h of its transform. At index 1 it
is eps/(pi(1+eps)); at index 2 it is not gamma times that, the first-order term in the step.

Units: the grid spacing is 1; S is in pixels^2, so sqrt(S) is the aperture in pixels.

Run: uv run records/affine/check-grid-matern-cross-shape.py
"""
import numpy as np


def rates(S):
    s12 = S[0, 1]
    a, c = S[0, 0] - abs(s12), S[1, 1] - abs(s12)
    assert a >= -1e-12 and c >= -1e-12, "S must be diagonally dominant"
    return a, c, max(s12, 0.0), max(-s12, 0.0)


def symbol(S, T1, T2):
    a, c, bp, bm = rates(S)
    return (a * (2 - 2 * np.cos(T1)) + c * (2 - 2 * np.cos(T2))
            + bp * (2 - 2 * np.cos(T1 + T2)) + bm * (2 - 2 * np.cos(T1 - T2)))


def increment(S, S2, gamma, n):
    th = 2 * np.pi * np.fft.fftfreq(n)
    T1, T2 = np.meshgrid(th, th, indexing="ij")
    rhohat = ((1 + symbol(S, T1, T2)) / (1 + symbol(S2, T1, T2))) ** gamma
    rho = np.real(np.fft.ifft2(rhohat))
    neg = -rho[rho < 0].sum()
    i = np.unravel_index(rho.argmin(), rho.shape)
    off = (i[0] if i[0] < n // 2 else i[0] - n, i[1] if i[1] < n // 2 else i[1] - n)
    return neg, rho[0, 0], off


def grid_n(S2):
    # torus large compared with the kernel's range (about sqrt of the largest eigenvalue)
    r = np.sqrt(np.linalg.eigvalsh(S2).max())
    return int(2 ** np.ceil(np.log2(max(256, 40 * r))))


def h_coeffs(eps, gamma, M=400, N=8192):
    # h(phi) = (<w, S w> / <w, S' w>)^gamma on the unit circle, for S = I, S' = diag(1+eps, 1): the
    # limit of the increment's transform along rays. It is even and pi-periodic,
    # h = a0 + sum_m a_m cos(2 m phi).
    phi = 2 * np.pi * np.arange(N) / N
    h = ((1 + eps) * np.cos(phi) ** 2 + np.sin(phi) ** 2) ** (-gamma)
    a = np.array([2 * np.mean(h * np.cos(2 * m * phi)) for m in range(1, M + 1)])
    return np.mean(h), a


def angular_factor(eps, gamma, theta, M=400):
    # The |x|^-2 term A(theta)/|x|^2 of the increment is the inverse transform of h - a0. In R^2
    # (rho(x) = (2 pi)^-2 int rhohat(w) e^{-i<w,x>} dw) the inverse transform of cos(2m phi) is
    # (-1)^m (m/pi) cos(2m theta)/|x|^2: Stein, Singular Integrals, ch. III, sec. 3.3, Thm. 5, the
    # transform of P_k(x)/|x|^{k+d} is gamma_k P_k(w)/|w|^k with
    # gamma_k = i^{-k} pi^{d/2} Gamma(k/2)/Gamma((k+d)/2), which for d = 2, k = 2m is (-1)^m pi/m.
    a0, a = h_coeffs(eps, gamma, M)
    m = np.arange(1, M + 1)
    return ((a * (-1.0) ** m * m / np.pi)[None, :] * np.cos(2 * np.outer(theta, m))).sum(axis=1)


def continuum_rate(eps, gamma):
    # The negative mass of A(theta)/|x|^2 on the shell a < |x| < 1 is log(1/a) int A_- d theta; with
    # the shells cut off at the grid scale, a ~ 1/t, this is the heuristic rate in log t. Returns the
    # rates of the negative and of the positive part, equal as A has mean zero.
    theta = 2 * np.pi * np.arange(20000) / 20000
    A = angular_factor(eps, gamma, theta)
    return np.mean(np.maximum(-A, 0)) * 2 * np.pi, np.mean(np.maximum(A, 0)) * 2 * np.pi


def main():
    print("calibration: ray step S -> 1.21 S (positive exactly)")
    for t in [2.0, 8.0, 32.0]:
        S = t**2 * np.diag([1.0, 0.5])
        neg, atom, _ = increment(S, 1.21 * S, 1, grid_n(1.21 * S))
        print(f"  aperture {t:5.1f}: negative mass {neg:.1e}")

    print("\nrank-one step S -> S + eps * t^2 * e1 e1' (widen one axis by a fraction eps), S = t^2 diag(1, 1):")
    print("  gamma  aperture   eps    negative mass   atom rho(0)   minimum at")
    for gamma in [1, 2]:
        for t in [2.0, 4.0, 8.0, 16.0, 32.0]:
            for eps in [0.01, 0.1, 0.5]:
                S = t**2 * np.eye(2)
                S2 = S + eps * t**2 * np.diag([1.0, 0.0])
                neg, atom, off = increment(S, S2, gamma, grid_n(S2))
                print(f"  {gamma:5d}  {t:8.1f}  {eps:5.2f}   {neg:13.3e}   {atom:11.4f}   {off}")

    print("\nfull-rank cross-shape step S -> S' with S = t^2 diag(1, 0.5), S' = t^2 diag(1.2, 0.55):")
    for gamma in [1, 2]:
        for t in [2.0, 8.0, 32.0]:
            S, S2 = t**2 * np.diag([1.0, 0.5]), t**2 * np.diag([1.2, 0.55])
            neg, atom, off = increment(S, S2, gamma, grid_n(S2))
            print(f"  gamma {gamma}, aperture {t:5.1f}: negative mass {neg:.3e}, atom {atom:.4f}, minimum at {off}")

    print("\nturning step: S = t^2 [[1, 0.3], [0.3, 1]] -> S + t^2 * 0.2 * v v', v = (1, -1)/sqrt 2")
    print("(widens the minor axis of S: a Loewner step that also turns the shape)")
    v = np.array([1.0, -1.0]) / np.sqrt(2)
    for t in [2.0, 8.0, 32.0]:
        S = t**2 * np.array([[1.0, 0.3], [0.3, 1.0]])
        S2 = S + 0.2 * t**2 * np.outer(v, v)
        neg, atom, off = increment(S, S2, 1, grid_n(S2))
        print(f"  aperture {t:5.1f}: negative mass {neg:.3e}, atom {atom:.4f}, minimum at {off}")

    print("\nslope of the negative mass in ln(aperture), against the first-order term in P,")
    print("(gamma/pi) * eps/(1+eps): at gamma = 1 the continuum rate, the density ~ (eps'/2pi) r^-2 cos(2 phi)")
    print("cut off at the grid; at gamma = 2 not the right comparison (the rates of the next block)")
    slopes = {}
    for gamma in [1, 2]:
        for eps in [0.01, 0.1, 0.5]:
            xs, ys = [], []
            for t in [4.0, 8.0, 16.0, 32.0]:
                S = t**2 * np.eye(2)
                S2 = S + eps * t**2 * np.diag([1.0, 0.0])
                xs.append(np.log(t))
                ys.append(increment(S, S2, gamma, grid_n(S2))[0])
            slope = np.polyfit(xs, ys, 1)[0]
            slopes[gamma, eps] = slope
            first = gamma / np.pi * eps / (1 + eps)
            print(f"  gamma {gamma}, eps {eps:4.2f}: measured {slope:.4f}, first-order term {first:.4f}")

    print("\nthe coefficient at every index: the continuum rate of the |x|^-2 term of the increment,")
    print("read off the degree-0 limit h of its transform, against the slopes above (t in {4, 8, 16, 32})")
    print("  gamma   eps    rate     slope    slope/rate   first-order term gamma*eps/(pi(1+eps))")
    for gamma in [1, 2]:
        for eps in [0.01, 0.1, 0.5]:
            rate, pos = continuum_rate(eps, gamma)
            assert abs(rate - pos) < 1e-9, "the angular factor has mean zero"
            first = gamma / np.pi * eps / (1 + eps)
            print(f"  {gamma:5d}  {eps:4.2f}   {rate:.4f}   {slopes[gamma, eps]:.4f}   "
                  f"{slopes[gamma, eps] / rate:10.3f}   {first:.4f}")
    print("(at gamma = 1 the rate is eps/(pi(1+eps)), Proposition E.4(4) of the paper, proved there by")
    print(" another route; this checks the constant and the sign of the method)")


if __name__ == "__main__":
    main()
