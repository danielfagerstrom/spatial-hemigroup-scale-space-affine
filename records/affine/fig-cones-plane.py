# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "matplotlib"]
# ///
"""Pass 6, the author's review of section 4.4 (2026-11-02): the figure of the invariant cones in the
plane (paper/fig-cones-plane.png), for the paragraph "A picture in the plane" of
paper/05-wedges.tex.

A symmetric 2 x 2 matrix is X = [[a+u, v], [v, a-u]], with eigenvalues a +- r, r = sqrt(u^2+v^2).
An O(2)-invariant closed convex cone containing I and no line is the round cone r <= k a. Drawn
are: (a) the section v = 0 through the axis, each cone the sector |u| <= k a; (b) the section
a = 1, each cone the disc r <= k. The openings drawn are k = 0 (the rays, C_0), k = 1/3 (C_1, the
cone of the Poisson kernel's orbit), k = 1/2 (C_2) and k = 1 (PSD(2), the Loewner order). The
shading is thm:wedge-axis(2) read in the plane: k < 1/2 non-Gaussian families, 1/2 <= k <= 1 the
affine Gaussian only, k > 1 none.

The script checks, before drawing, the three facts the paragraph and the caption state:
  1. C_alpha of prop:stable-order-generated, {X >= 0 : (2+alpha) lambda_min(X) >= tr X}, is the
     round cone of opening k = alpha/(alpha+2), on random symmetric matrices, for several alpha;
  2. PSD(2) is the round cone of opening 1;
  3. for the round cone of opening k < 1, beta(C) = max (tr X / lambda_min(X) - d) = 2k/(1-k)
     (thm:wedge-axis(2)(c)), so beta < 2 exactly when k < 1/2.
It prints the checks and the openings. Nothing in the paper reads these numbers.

Drawn at the printed width (6.26 in = \\textwidth), so the 8-9 pt labels print at 8-9 pt.

Run from the repository root:
    uv run records/affine/fig-cones-plane.py > records/affine/fig-cones-plane-output.txt
"""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "paper" / "fig-cones-plane.png"
rng = np.random.default_rng(20261102)


def coords(X):
    a = 0.5 * (X[0, 0] + X[1, 1])
    u = 0.5 * (X[0, 0] - X[1, 1])
    v = X[0, 1]
    return a, np.hypot(u, v)


def in_C_alpha(X, alpha, d=2):
    lam = np.linalg.eigvalsh(X)
    return lam[0] >= -1e-12 and (d + alpha) * lam[0] >= np.trace(X) - 1e-12


def check():
    n = 20000
    for alpha in (0.25, 1.0, 1.5, 2.0, 5.0, 40.0):
        k = alpha / (alpha + 2)
        bad = 0
        for _ in range(n):
            B = rng.normal(size=(2, 2))
            X = B + B.T
            a, r = coords(X)
            if abs(r - k * a) < 1e-9:
                continue
            if in_C_alpha(X, alpha) != (a >= 0 and r <= k * a):
                bad += 1
        print(f"  C_alpha, alpha = {alpha:5.2f}: round cone of opening k = {k:.6f}; "
              f"{n} random X, {bad} disagreements")
        assert bad == 0
    bad = 0
    for _ in range(n):
        B = rng.normal(size=(2, 2))
        X = B + B.T
        a, r = coords(X)
        if abs(r - a) < 1e-9:
            continue
        if (np.linalg.eigvalsh(X)[0] >= 0) != (r <= a):
            bad += 1
    print(f"  PSD(2): round cone of opening k = 1; {n} random X, {bad} disagreements")
    assert bad == 0
    for k in (0.0, 1 / 3, 0.5, 0.8):
        # members of the cone with a = 1: r in [0, k]; tr X / lambda_min - 2 = 2/(1-r) - 2
        rs = np.linspace(0, k, 2001)
        beta = np.max(2 / (1 - rs) - 2)
        print(f"  round cone k = {k:.6f}: beta(C) = {beta:.6f}, 2k/(1-k) = {2 * k / (1 - k):.6f}")
        assert abs(beta - 2 * k / (1 - k)) < 1e-9


def draw():
    cones = [  # (k, label, style)
        (1 / 3, r"$C_1$, $k = \frac{1}{3}$", dict(color="C0", lw=1.6)),
        (0.5, r"$C_2$, $k = \frac{1}{2}$", dict(color="C3", lw=1.4, ls="--")),
        (1.0, r"$\mathrm{PSD}(2)$, $k = 1$", dict(color="0.2", lw=1.6)),
    ]
    plt.rcParams.update({"font.size": 9})
    green, amber, grey = "#cfe8cf", "#f6e3b4", "#e6e6e6"
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.26, 3.06), gridspec_kw=dict(width_ratios=[1.35, 1]))

    # (a) the section v = 0: sectors |u| <= k a
    A = 1.1
    U = 1.25
    ax1.fill_between([-U, U], [A, A], [0, 0], color=grey, lw=0, zorder=0)
    ax1.fill([0, -A, A], [0, A, A], color=amber, lw=0, zorder=1)
    ax1.fill([0, -0.5 * A, 0.5 * A], [0, A, A], color=green, lw=0, zorder=2)
    for k, label, style in cones:
        ax1.plot([-k * A, 0, k * A], [A, 0, A], label=label, zorder=3, **style)
    ax1.plot([0, 0], [0, A], color="k", lw=2.2, label=r"rays, $k = 0$", zorder=4)
    ax1.set_xlim(-U, U)
    ax1.set_ylim(-0.05, A)
    ax1.set_xlabel(r"$u$, change of shape")
    ax1.set_ylabel(r"$a$, growth in size")
    ax1.set_title(r"(a) the section $v = 0$", fontsize=9)
    ax1.set_aspect("equal")

    # (b) the section a = 1: discs r <= k
    R = 1.35
    ax2.add_patch(plt.Rectangle((-R, -R), 2 * R, 2 * R, color=grey, lw=0, zorder=0))
    ax2.add_patch(plt.Circle((0, 0), 1.0, color=amber, lw=0, zorder=1))
    ax2.add_patch(plt.Circle((0, 0), 0.5, color=green, lw=0, zorder=2))
    t = np.linspace(0, 2 * np.pi, 400)
    for k, _label, style in cones:
        ax2.plot(k * np.cos(t), k * np.sin(t), zorder=3, **style)
    ax2.plot([0], [0], "o", color="k", ms=4, zorder=4)
    ax2.text(0.0, -0.08, "rays", fontsize=8, ha="center", va="top", zorder=5)
    arrow = dict(arrowstyle="->", color="0.25", lw=0.8)
    ax2.annotate("non-Gaussian families", xy=(0.0, 0.42), xytext=(0.0, 1.2), fontsize=8,
                 ha="center", va="center", arrowprops=arrow, zorder=5)
    ax2.annotate("the affine Gaussian only", xy=(-0.55, -0.55), xytext=(-1.28, -1.22), fontsize=8,
                 ha="left", va="center", arrowprops=arrow, zorder=5)
    ax2.text(1.28, -1.22, "no family", fontsize=8, ha="right", va="center", zorder=5)
    ax2.set_xlim(-R, R)
    ax2.set_ylim(-R, R)
    ax2.set_xlabel(r"$u$")
    ax2.set_ylabel(r"$v$", rotation=0, labelpad=6)
    ax2.set_title(r"(b) the section $a = 1$", fontsize=9)
    ax2.set_aspect("equal")
    for ax in (ax1, ax2):
        ax.set_xticks([])
        ax.set_yticks([])
    handles, labels = ax1.get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=4, fontsize=8, frameon=False)
    fig.tight_layout(rect=(0, 0.08, 1, 1))
    fig.savefig(OUT, dpi=200)
    print(f"wrote {OUT.relative_to(ROOT).as_posix()}")


def main():
    print("Invariant cones in the plane: X = [[a+u, v], [v, a-u]], round cones r <= k a")
    check()
    for alpha in (0.0, 1.0, 2.0):
        print(f"  opening of C_{alpha:g}: k = {alpha / (alpha + 2):.6f}")
    draw()


main()
