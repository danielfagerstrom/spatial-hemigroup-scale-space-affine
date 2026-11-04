# /// script
# dependencies = ["numpy"]
# ///
"""A Gaussian part makes a shape-carrying Matern step positive without making it infinitely divisible.

Cited by the annotation of prop:similarity-orbit-family (Q-0246 item 3). Run: `uv run
records/affine/check-gaussian-matern-step.py` (about a minute).

The family, in the plane: mu_Sigma = N(0, 2b Sigma) * M_{h(Sigma)}, where M_H is the Matern orbit of
index 1, transform (1 + <w,Hw>)^(-1), and h(Sigma) = Sigma + kappa tr(Sigma) I. The increment of the
Loewner step Sigma -> Sigma + P has transform

    rho^(w) = exp(-b <w,Pw>) (1 + <w,Hw>) / (1 + <w,H'w>),   H = h(Sigma), H' = h(Sigma + P),

and its density is computed by FFT. If the increment were infinitely divisible, uniqueness of the
generating triplet would make its Levy measure n_{H'} - n_H, which is signed whenever H' is not a
multiple of H (prop:orbit-step-cone(3), a profile bounded at the origin). So a positive increment
with H' not proportional to H is a positive increment that is not infinitely divisible.

Calibration: ray steps (P a multiple of Sigma, so H' a multiple of H) are positive measures by
prop:affine-orbits(4); their computed minima measure the numerical floor.
"""
import numpy as np


def h(S, kappa):
    return S + kappa * np.trace(S) * np.eye(2)


def increment(S, P, b, kappa, n=2048, span=60.0):
    """Return (min/max of the density, negative mass, |x| of the minimum / scale)."""
    H, H2 = h(S, kappa), h(S + P, kappa)
    scale = np.sqrt(max(np.linalg.eigvalsh(H2).max(), 2 * b * np.linalg.eigvalsh(P).max()))
    L = span * scale
    dx = L / n
    x = (np.arange(n) - n // 2) * dx
    w = 2 * np.pi * np.fft.fftfreq(n, d=dx)
    W1, W2 = np.meshgrid(w, w, indexing="ij")

    def q(M):
        return M[0, 0] * W1**2 + 2 * M[0, 1] * W1 * W2 + M[1, 1] * W2**2

    rhohat = np.exp(-b * q(P)) * (1 + q(H)) / (1 + q(H2))
    dens = np.fft.fftshift(np.real(np.fft.ifft2(rhohat))) / dx**2
    i = np.unravel_index(dens.argmin(), dens.shape)
    negmass = -dens[dens < 0].sum() * dx * dx
    return dens.min() / dens.max(), negmass, np.hypot(x[i[0]], x[i[1]]) / scale


def main():
    S = np.diag([1.0, 0.3])
    print("calibration, ray step P = S (positive by prop:affine-orbits(4)):")
    for b in [0.1, 0.5, 2.0]:
        r, neg, _ = increment(S, S, b, 2.0)
        print(f"  b = {b:4.1f}: min/max {r:+.1e}, negative mass {neg:.1e}")
    P = np.diag([0.05, 0.55])
    print("cross-shape step P = diag(0.05, 0.55); H' is not a multiple of H:")
    for b in [0.1, 0.5, 2.0, 8.0]:
        for kappa in [0.5, 2.0]:
            for n in [1024, 2048]:
                r, neg, where = increment(S, P, b, kappa, n=n)
                print(f"  b = {b:4.1f}, kappa = {kappa}, n = {n}: min/max {r:+.1e}, "
                      f"negative mass {neg:.1e}, minimum at |x|/scale = {where:.2f}")


if __name__ == "__main__":
    main()
