# /// script
# dependencies = ["numpy"]
# ///
"""Round 3, report D, suggestion 7: Remark E.5's grid check for a step rotated by 45 degrees.

The step t^2 I -> t^2 (I + eps v v^T), v = (1, 1)/sqrt 2, has the same continuum rate
eps/(pi(1+eps)) as the diagonal step (the rate is rotation invariant); on the grid it uses the
diagonal neighbours (b_+ > 0). Referee D reports slope 0.1092 against 0.1061 at gamma = 1, eps = 0.5.

Run: python3 records/affine/reviews/verify-round3-paper-scripts/e5_rotated_step.py
"""
import numpy as np


def symbol(S, T1, T2):
    s12 = S[0, 1]
    a, c = S[0, 0] - abs(s12), S[1, 1] - abs(s12)
    bp, bm = max(s12, 0.0), max(-s12, 0.0)
    return (a * (2 - 2 * np.cos(T1)) + c * (2 - 2 * np.cos(T2))
            + bp * (2 - 2 * np.cos(T1 + T2)) + bm * (2 - 2 * np.cos(T1 - T2)))


def neg_mass(S, S2, gamma, n):
    th = 2 * np.pi * np.fft.fftfreq(n)
    T1, T2 = np.meshgrid(th, th, indexing="ij")
    rho = np.real(np.fft.ifft2(((1 + symbol(S, T1, T2)) / (1 + symbol(S2, T1, T2))) ** gamma))
    return -rho[rho < 0].sum()


def main():
    eps, gamma = 0.5, 1
    v = np.array([1.0, 1.0]) / np.sqrt(2)
    for name, P in [("diagonal", np.diag([1.0, 0.0])), ("rotated 45", np.outer(v, v))]:
        ts = [4, 8, 16, 32]
        ys = [neg_mass(t**2 * np.eye(2), t**2 * (np.eye(2) + eps * P), gamma, 64 * t) for t in ts]
        print(f"{name:10s}: slope {np.polyfit(np.log(ts), ys, 1)[0]:.4f}  (continuum {eps/(np.pi*(1+eps)):.4f})")


if __name__ == "__main__":
    main()
