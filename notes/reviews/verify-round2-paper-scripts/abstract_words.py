"""Count the words of the affine paper's abstract, and of candidate rewordings, with the
convention of paper/main.tex's abstract comment: each inline math span counts as one word,
comments are dropped, \\Matern{} is one word.

Usage: python3 abstract_words.py <repo root>
"""
import re
import sys

root = sys.argv[1]
tex = open(f"{root}/paper/main.tex", encoding="utf-8").read()
body = tex.split("\\begin{abstract}")[1].split("\\end{abstract}")[0]


def count(s):
    s = re.sub(r"(?m)%.*$", "", s)
    s = re.sub(r"\$[^$]*\$", " M ", s)
    s = s.replace("\\Matern{}", "Matern").replace("~", " ")
    return len(s.split())


print("abstract as built:", count(body))

# Candidate replacements (old -> new) proposed in VERIFY-round2-front-paper.md, item 2.
CANDIDATES = {
    "2.1 covariance matrices": (
        "an order $W$ on covariance matrices",
        "an order $W$ on the aperture matrices",
    ),
    "2.2 alpha (variant)": (
        "a non-Gaussian kernel pays in speed of shape change.",
        "a non-Gaussian kernel pays in speed of shape change: the index bounds the anisotropy a "
        "step gains for its growth in volume.",
    ),
    "2.3 re-measurement": (
        "only the Gaussian reaches them by further smoothing.",
        "only the Gaussian reaches them by further smoothing, and for every other kernel the "
        "adapted record is a new measurement of the image.",
    ),
}
for name, (old, new) in CANDIDATES.items():
    assert old in re.sub(r"\s+", " ", body), name
    print(f"{name}: {count(old)} -> {count(new)} words ({count(new) - count(old):+d})")

# The reviewer's item 2 replacement against the three passages it replaces (its "..." elided).
OLD = [
    "Under hemigroup axioms both are: a family is given by a group $G$ of linear maps it respects "
    "and an order $W$ on covariance matrices along which coarser records further smooth finer ones.",
    "Shape-adapted apertures are such steps from the first stage; among linear images of "
    "rotation-invariant laws with a positive transform only the Gaussian reaches them by further "
    "smoothing. Along a chain of orders from the rays ($\\alpha = 0$) to the Loewner order "
    "($\\alpha = \\infty$), a non-Gaussian kernel pays in speed of shape change.",
]
NEW = [
    "Under hemigroup axioms both are: a family is specified by a covariance group $G$ of linear maps "
    "of the image and a partial order $W$ on positive semidefinite scale-shape matrices $\\Sigma$ "
    "(proportional to the covariance in the Gaussian case) along which coarser records are further "
    "smoothings of finer ones.",
    "In standard shape-adapted smoothing, the step from the isotropic first stage to an adapted "
    "aperture preserves the minimum directional scale and is therefore rank-deficient; among linear "
    "images of rotation-invariant laws with a positive Fourier transform, only the Gaussian reaches "
    "the adapted aperture by further smoothing of the first stage, whereas every other kernel must "
    "either convolve the original image afresh (as the Lindeberg-Garding iteration already does) or "
    "increase its minimum scale. Along a continuous chain of $GL(d)$-invariant orders indexed by "
    "$0 \\le \\alpha \\le \\infty$-where $\\alpha$ bounds how fast the aperture's anisotropy may grow "
    "relative to its volume scale, from pure rescalings along rays ($\\alpha = 0$) to the full "
    "Loewner order ($\\alpha = \\infty$)-a non-Gaussian kernel pays in maximum speed of shape change.",
]
o, n = sum(count(s) for s in OLD), sum(count(s) for s in NEW)
print(f"reviewer's item 2 replacement: {o} -> {n} words ({n - o:+d}); abstract would be {count(body) + n - o}")
