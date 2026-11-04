# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "matplotlib"]
# ///
"""Q-0290, review flag V1: the figure of the d = 2 shape plane (paper/fig-shape-plane.png).

Panel (a): the shapes reachable from the isotropic aperture Sigma_1 = t_1^2 I by one step to volume
scale t_2 = 2 t_1, in a chart of the shapes S with det S = 1: the radius is the distance
delta(I, S) = (log^2 n_1 + log^2 n_2)^{1/2} of lem:loewner-scale-shape(4) and the angle is twice the
orientation of the major axis. Around S_1 = I the reachable sets are discs:
  - the Loewner order, delta <= 2 sqrt(2) log(t_2/t_1)               (lem:loewner-scale-shape(4));
  - the stable order of index alpha, delta <= 2 sqrt(2) alpha/(2+alpha) log(t_2/t_1)
    (prop:stable-step-cone(3) at d = 2: n_1 >= (t_1/t_2)^{2 alpha/(2+alpha)});
  - the rays, the centre alone.
Panel (b): the same orders as wedges in the half-plane of (log(t_2/t_1), log of the anisotropy gained,
sqrt(n_2/n_1)): slopes d = 2 (Loewner) and d alpha/(d+alpha) (stable), 0 (rays). The apertures
t M of shape-adapted smoothing (M with least eigenvalue 1, prop:shape-adapted-apertures) lie on the
Loewner edge: from t I, log(t_2/t_1) = (1/4) log m and the anisotropy is sqrt(m).

The chart in (a) is a choice of coordinates, not the hyperbolic metric's picture; no statement uses
the figure. The script checks the discs against the defining inequalities on random shapes (the
Loewner order by the least eigenvalue of Sigma_2 - Sigma_1, the stable order by condition (c) of
prop:stable-step-cone(1)) and prints the radii and the checks.

Run from the repository root:
    uv run records/affine/fig-shape-plane.py > records/affine/fig-shape-plane-output.txt
"""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "paper" / "fig-shape-plane.png"
D = 2
RATIO = 2.0                       # t_2 / t_1 in panel (a)
ALPHAS = [0.5, 1.0, 1.5]
INK = "#52514e"                   # Loewner, axes text
BLUES = {0.5: "#86b6ef", 1.0: "#3987e5", 1.5: "#1c5cab"}   # ordinal blue steps 250, 400, 550
PRACTICE = "#eb6834"              # categorical slot 2
LOEWNER_FILL = "#f0efec"


def shape(u, theta):
    """det-1 shape with eigenvalues e^{-u} <= e^{u}, major axis at angle theta."""
    c, s = np.cos(theta), np.sin(theta)
    q = np.array([[c, -s], [s, c]])
    return q @ np.diag([np.exp(u), np.exp(-u)]) @ q.T


def delta_from_identity(s):
    ev = np.linalg.eigvalsh(s)
    return float(np.sqrt(np.sum(np.log(ev) ** 2)))


def loewner(sig1, sig2):
    return np.linalg.eigvalsh(sig2 - sig1).min() >= -1e-12


def stable(sig1, sig2, alpha):
    w, v = np.linalg.eigh(sig1)
    r = v @ np.diag(w ** -0.5) @ v.T
    m = r @ sig2 @ r
    ev = np.linalg.eigvalsh(m)
    return ev.min() ** (D + alpha) >= np.prod(ev) * (1 - 1e-12)


def radius_loewner(ratio):
    return 2 * np.sqrt(2) * np.log(ratio)


def radius_stable(ratio, alpha):
    return 2 * np.sqrt(2) * alpha / (D + alpha) * np.log(ratio)


def checks(n=20000, seed=1):
    rng = np.random.default_rng(seed)
    bad = {"loewner": 0, **{a: 0 for a in ALPHAS}}
    near = 1e-9
    for _ in range(n):
        ratio = np.exp(rng.uniform(0.0, 1.2))
        u = rng.uniform(0.0, 2.0)
        s = shape(u, rng.uniform(0, np.pi))
        dl = delta_from_identity(s)
        sig1, sig2 = np.eye(2), ratio ** 2 * s
        rl = radius_loewner(ratio)
        if abs(dl - rl) > near and loewner(sig1, sig2) != (dl <= rl):
            bad["loewner"] += 1
        for a in ALPHAS:
            ra = radius_stable(ratio, a)
            if abs(dl - ra) > near and stable(sig1, sig2, a) != (dl <= ra):
                bad[a] += 1
    return n, bad


def practice_points(ms):
    """(log t2/t1, log anisotropy) of the aperture t M, M = diag(1, m), seen from t I."""
    pts = []
    for m in ms:
        t = 1.0
        sig1, sig2 = t * np.eye(2), t * np.diag([1.0, m])
        t1 = np.linalg.det(sig1) ** (1 / (2 * D))
        t2 = np.linalg.det(sig2) ** (1 / (2 * D))
        ev = np.linalg.eigvalsh(sig2 / t2 ** 2)
        assert loewner(sig1, sig2)
        pts.append((np.log(t2 / t1), 0.5 * np.log(ev.max() / ev.min())))
    return pts


def main():
    print(f"Shape plane, d = {D}, step to volume scale t2 = {RATIO:g} t1 from Sigma_1 = t1^2 I")
    print(f"  Loewner disc radius  2 sqrt2 log(t2/t1)                = {radius_loewner(RATIO):.4f}")
    for a in ALPHAS:
        print(f"  stable alpha = {a:3.1f}: radius 2 sqrt2 a/(2+a) log(t2/t1) = {radius_stable(RATIO, a):.4f}"
              f"   max anisotropy (t2/t1)^(2a/(2+a)) = {RATIO ** (2 * a / (2 + a)):.4f}")
    print(f"  Loewner max anisotropy (t2/t1)^d = {RATIO ** D:.4f}")
    n, bad = checks()
    print(f"\nCheck on {n} random steps (ratio in [1, e^1.2], log-anisotropy u in [0, 2]):")
    print(f"  Loewner order <=> inside the Loewner disc: {n - bad['loewner']} agree, {bad['loewner']} disagree")
    for a in ALPHAS:
        print(f"  stable order a = {a:3.1f} <=> inside its disc:     {n - bad[a]} agree, {bad[a]} disagree")
    ms = [2.0, 4.0, 8.0, 16.0]
    pts = practice_points(ms)
    print("\nShape-adapted apertures t diag(1, m) from t I (slope 2 is the Loewner edge):")
    for m, (x, y) in zip(ms, pts):
        print(f"  m = {m:4.0f}: log(t2/t1) = {x:.4f}, log anisotropy = {y:.4f}, ratio = {y / x:.4f}")

    plt.rcParams.update({"font.size": 8, "axes.edgecolor": INK, "axes.labelcolor": INK,
                         "xtick.color": INK, "ytick.color": INK, "text.color": "#0b0b0b"})
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.3, 3.0), gridspec_kw={"width_ratios": [1, 1.15]})

    # (a) the discs
    phi = np.linspace(0, 2 * np.pi, 400)
    rl = radius_loewner(RATIO)
    ax.fill(rl * np.cos(phi), rl * np.sin(phi), color=LOEWNER_FILL, zorder=0)
    ax.plot(rl * np.cos(phi), rl * np.sin(phi), color=INK, lw=1.4, zorder=2)
    ax.text(0.0, -rl - 0.1, "Loewner", ha="center", va="top", color=INK)
    for k, a in enumerate(ALPHAS):
        r = radius_stable(RATIO, a)
        ax.plot(r * np.cos(phi), r * np.sin(phi), color=BLUES[a], lw=1.4, zorder=3)
        ang = np.deg2rad(-60 + 30 * k)
        ax.annotate(fr"$\alpha={a:g}$", (r * np.cos(ang), r * np.sin(ang)),
                    xytext=(rl + 0.2, -1.35 + 0.4 * k), color=INK, va="center",
                    arrowprops={"arrowstyle": "-", "color": BLUES[a], "lw": 0.8})
    ax.plot([0], [0], "o", color="#0b0b0b", ms=4, zorder=4)
    ax.annotate("rays", (0, 0), xytext=(-2.0, 1.75), color=INK,
                arrowprops={"arrowstyle": "-", "color": INK, "lw": 0.8})
    # aperture glyphs at the Loewner edge, three orientations
    for th in (0.0, np.pi / 4, np.pi / 2):
        u = rl / np.sqrt(2)
        cx, cy = rl * np.cos(2 * th), rl * np.sin(2 * th)
        s = shape(u, th)
        w, v = np.linalg.eigh(s)
        e = v @ np.diag(np.sqrt(w)) @ np.vstack([np.cos(phi), np.sin(phi)]) * 0.16
        ax.plot(cx + e[0], cy + e[1], color=INK, lw=0.7, zorder=5)
    lim = rl + 0.45
    ax.set_xlim(-lim, lim + 0.9)
    ax.set_ylim(-lim, lim)
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for sp in ax.spines.values():
        sp.set_visible(False)
    ax.set_title(r"(a) shapes reachable from $t_1^2I$ at $t_2 = 2t_1$", fontsize=8, color="#0b0b0b")

    # (b) the wedges
    xmax = 1.1
    x = np.linspace(0, xmax, 50)
    bx.fill_between(x, 0, D * x, color=LOEWNER_FILL, zorder=0)
    bx.plot(x, D * x, color=INK, lw=1.4, zorder=2)
    bx.text(0.98, D * 0.98, r"Loewner, slope $d = 2$", ha="right", va="bottom", color=INK)
    for a in ALPHAS:
        sl = D * a / (D + a)
        bx.plot(x, sl * x, color=BLUES[a], lw=1.4, zorder=3)
        bx.text(xmax + 0.02, sl * xmax, fr"$\alpha={a:g}$", ha="left", va="center", color=INK)
    bx.plot(x, 0 * x, color="#0b0b0b", lw=1.4, zorder=3)
    bx.text(xmax + 0.02, 0.06, "rays", ha="left", va="bottom", color=INK)
    px, py = zip(*pts)
    bx.plot(px, py, "x", color=PRACTICE, ms=6, mew=1.5, zorder=6)
    # Q-0312 (review flag 29): no "tM" in the label; t is a volume scale on the horizontal axis
    bx.annotate("shape-adapted\napertures", (px[1], py[1]), xytext=(0.12, 1.35), color=INK,
                arrowprops={"arrowstyle": "-", "color": PRACTICE, "lw": 0.8})
    # Q-0312 / review item 10: the slanted-surface example (60 degrees, n_2/n_1 = 4), from the Loewner
    # line to the alpha = 1 line at the same anisotropy log 2: x = log2/2 = 0.347 to log2 * (d+a)/(d a) = 1.040
    ay = np.log(4) / 2
    ax_start, ax_end = ay / D, ay * (D + 1.0) / (D * 1.0)
    bx.annotate("", xy=(ax_end, ay), xytext=(ax_start, ay),
                arrowprops={"arrowstyle": "->", "color": INK, "lw": 0.9, "ls": "--"}, zorder=5)
    bx.text(0.65, ay + 0.07, "slanted\nsurface", ha="center", va="bottom", color=INK)
    print(f"\nSlanted-surface arrow at log anisotropy {ay:.4f}: from x = {ax_start:.4f} to x = {ax_end:.4f}")
    bx.set_xlim(0, 1.35)
    bx.set_ylim(-0.05, 2.1)
    bx.set_xlabel(r"$\log(t_2/t_1)$")
    bx.set_ylabel(r"$\log$ of the anisotropy gained, $\log\sqrt{n_2/n_1}$")
    for side in ("top", "right"):
        bx.spines[side].set_visible(False)
    bx.set_title("(b) the orders as wedges", fontsize=8, color="#0b0b0b")

    fig.tight_layout()
    fig.savefig(OUT, dpi=220)
    print(f"\nwrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
