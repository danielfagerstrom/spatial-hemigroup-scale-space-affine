# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "matplotlib"]
# ///
"""Q-0289, review flag 39: the schematic of the paper's section 4.4 (paper/fig-rank-deficient-step.png).

A rank-one Loewner step in the plane, from Sigma = I to Sigma + P with P = p u u^T, p = 1.5, and u
the unit vector at 30 degrees. Drawn are the aperture ellipses {x : <x, Sigma^{-1} x> = 1} of the
two matrices, the range R u of P, and the two lines <x, w> = +-1, w = u rotated by 90 degrees,
which span ker P. The support function of the ellipse of a matrix S is h_S(w) = sqrt(<w, S w>), so
h_{Sigma+P}(w) = h_Sigma(w) for w in ker P: both ellipses touch both lines. The script checks this
numerically and prints the two support values in the directions u and w.

Nothing in the paper reads these numbers; the figure illustrates thm:rank-deficient-step.

Drawn at the printed width (3.13 in = 0.5 \\textwidth), so the 8-9 pt labels print at 8-9 pt.

Run from the repository root:
    uv run records/affine/fig-rank-deficient-step.py > records/affine/fig-rank-deficient-step-output.txt
"""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "paper" / "fig-rank-deficient-step.png"

theta = np.deg2rad(30.0)
u = np.array([np.cos(theta), np.sin(theta)])
w = np.array([-np.sin(theta), np.cos(theta)])
p = 1.5
Sigma = np.eye(2)
P = p * np.outer(u, u)
Sigma2 = Sigma + P


def ellipse(S, n=400):
    """Boundary of {x : <x, S^{-1} x> <= 1}, the image of the unit circle under S^{1/2}."""
    vals, vecs = np.linalg.eigh(S)
    root = vecs @ np.diag(np.sqrt(vals)) @ vecs.T
    t = np.linspace(0, 2 * np.pi, n)
    return root @ np.vstack([np.cos(t), np.sin(t)])


def support(S, v):
    return float(np.sqrt(v @ S @ v))


def main():
    print("Rank-one Loewner step Sigma = I -> Sigma + P, P = p u u^T, p = 1.5, u at 30 degrees")
    for name, v in (("u (range of P)", u), ("w (ker P)", w)):
        print(f"  support in direction {name:15s}: Sigma {support(Sigma, v):.6f}   "
              f"Sigma+P {support(Sigma2, v):.6f}")
    assert abs(support(Sigma, w) - support(Sigma2, w)) < 1e-12
    assert abs(support(Sigma2, u) - np.sqrt(1 + p)) < 1e-12

    fig, ax = plt.subplots(figsize=(3.13, 3.45))
    e1, e2 = ellipse(Sigma), ellipse(Sigma2)
    ax.plot(e1[0], e1[1], color="0.35", lw=1.4, label=r"$\Sigma = I$")
    ax.plot(e2[0], e2[1], color="C0", lw=1.8, label=r"$\Sigma + P$")
    L = 2.4
    ax.plot([-L * u[0], L * u[0]], [-L * u[1], L * u[1]], color="C3", lw=1.0,
            label=r"range of $P$")
    for s in (1.0, -1.0):
        base = s * w
        ax.plot([base[0] - L * u[0], base[0] + L * u[0]],
                [base[1] - L * u[1], base[1] + L * u[1]],
                color="0.5", lw=0.9, ls="--",
                label=r"$\langle x, w\rangle = \pm 1$, $w \in \ker P$" if s > 0 else None)
    ax.annotate("", xy=1.0 * w, xytext=(0, 0),
                arrowprops=dict(arrowstyle="->", color="0.3", lw=0.9))
    ax.text(1.08 * w[0] - 0.05, 1.08 * w[1], r"$w$", fontsize=9)
    ax.set_aspect("equal")
    ax.set_xlim(-2.0, 2.0)
    ax.set_ylim(-1.9, 1.9)
    ax.axhline(0, color="0.85", lw=0.6, zorder=0)
    ax.axvline(0, color="0.85", lw=0.6, zorder=0)
    ax.set_xticks([])
    ax.set_yticks([])
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.02), ncol=2, fontsize=8, frameon=False,
              columnspacing=1.0, handlelength=1.6)
    fig.tight_layout()
    fig.savefig(OUT, dpi=300)
    print(f"wrote {OUT.relative_to(ROOT)}")


main()
