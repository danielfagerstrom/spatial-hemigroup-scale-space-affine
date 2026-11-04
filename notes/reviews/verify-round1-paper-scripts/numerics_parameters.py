# /// script
# dependencies = ["numpy"]
# ///
"""Round-1 verification (Gemini report, section 4): the discretization parameters of Remarks E.5 and H.3.

Reads the parameters off the two deposited scripts by importing them (no copy of their logic), and
prints what the printed remarks would have to state for a reader to reproduce the numbers:

  Remark E.5 (records/affine/check-grid-matern-cross-shape.py): for each (gamma, t, eps) of the fitted
  slopes, the torus size n chosen by grid_n, and the stencil rates (a, c, bp, bm) of S and S'. The
  diagonal rates bp, bm vanish for diagonal S, so the "nine-point" stencil reduces to five points.

  Remark H.3 (records/affine/check-gaussian-matern-step.py): for the printed step and kappa = 2, b in
  {0.1, 2}, the box side L, the spacing dx and the Nyquist frequency pi/dx at n = 1024 and 2048, and
  the direction of the density's minimum at b = 0.1.

Run: python3 -I records/affine/reviews/verify-round1-paper-scripts/numerics_parameters.py
"""
import importlib.util
import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(sys.argv[0]).resolve().parents[2]  # records/affine


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), ROOT / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def remark_e5():
    g = load("check-grid-matern-cross-shape")
    print("Remark E.5: torus size n and stencil rates (a, c, bp, bm) of D_S")
    print("  t     eps    n      rates of S = t^2 I          rates of S' = t^2 diag(1+eps, 1)")
    for t in [4.0, 8.0, 16.0, 32.0]:
        for eps in [0.01, 0.1, 0.5]:
            S = t**2 * np.eye(2)
            S2 = S + eps * t**2 * np.diag([1.0, 0.0])
            n = g.grid_n(S2)
            r1 = tuple(round(float(v), 3) + 0.0 for v in g.rates(S))
            r2 = tuple(round(float(v), 3) + 0.0 for v in g.rates(S2))
            print(f"  {t:4.0f}  {eps:4.2f}  {n:5d}  {r1!s:28}  {r2}")
    print("  (bp = bm = 0 throughout: the diagonal neighbours carry weight zero, five points remain)")


def remark_h3():
    m = load("check-gaussian-matern-step")
    S = np.diag([1.0, 0.3])
    P = np.diag([0.05, 0.55])
    kappa = 2.0
    print("\nRemark H.3: box and resolution, kappa = 2, span = 60 x scale (defaults of increment())")
    for b in [0.1, 2.0]:
        H2 = m.h(S + P, kappa)
        scale = np.sqrt(max(np.linalg.eigvalsh(H2).max(), 2 * b * np.linalg.eigvalsh(P).max()))
        L = 60.0 * scale
        for n in [1024, 2048]:
            dx = L / n
            print(f"  b = {b:3.1f}, n = {n}: scale {scale:.4f}, box side L = {L:.2f}, "
                  f"dx = {dx:.4f}, Nyquist pi/dx = {np.pi / dx:.1f}")
    # direction of the minimum at b = 0.1 (recomputed with the deposited formula)
    b, n = 0.1, 2048
    H, H2 = m.h(S, kappa), m.h(S + P, kappa)
    scale = np.sqrt(max(np.linalg.eigvalsh(H2).max(), 2 * b * np.linalg.eigvalsh(P).max()))
    L = 60.0 * scale
    dx = L / n
    x = (np.arange(n) - n // 2) * dx
    w = 2 * np.pi * np.fft.fftfreq(n, d=dx)
    W1, W2 = np.meshgrid(w, w, indexing="ij")

    def q(M):
        return M[0, 0] * W1**2 + 2 * M[0, 1] * W1 * W2 + M[1, 1] * W2**2

    rhohat = np.exp(-b * q(P)) * (1 + q(H)) / (1 + q(H2))
    dens = np.fft.fftshift(np.real(np.fft.ifft2(rhohat))) / dx**2
    i = np.unravel_index(dens.argmin(), dens.shape)
    print(f"  b = 0.1, n = 2048: minimum at x = ({x[i[0]]:+.3f}, {x[i[1]]:+.3f})")
    Hm = np.diag(1 / np.sqrt(np.diag(H)))
    print(f"  relative step H^-1/2 (H'-H) H^-1/2 = diag{tuple(round(float(v), 3) for v in np.diag(Hm @ (H2 - H) @ Hm))}"
          " (least widened direction: e1)")


if __name__ == "__main__":
    remark_e5()
    remark_h3()
