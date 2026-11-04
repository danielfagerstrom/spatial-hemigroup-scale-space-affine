"""Report B, part 3 (viii): an (S(d), rays) family whose kernel at a positive definite aperture is
delta_0.

The referee's map, d = 2 and 3: nu_S = N(0, phi(sigma(S)) tr(S) I) for S != 0, nu_0 = delta_0,
with sigma(S) the eigenvalues of S in nonincreasing order divided by tr S (Proposition F.3) and
phi continuous on the simplex, phi(1/d,...,1/d) = 1, phi(sigma0) = 0 at an interior sigma0.
The choice made here:
    phi(s) = |s - sigma0| / (|s - sigma0| + |s - c|),  c = (1/d, ..., 1/d),
which is continuous on the simplex, 1 at c, 0 at sigma0, values in [0, 1].
Checked: (a) nu_0 = delta_0, nu_I != delta_0; (b) covariance under random similarities cQ;
(c) continuity of the covariance on PSD(d), at the origin and across eigenvalue crossings and
singular matrices (sampled); every nu_S is Gaussian or delta_0, hence self-decomposable.
By Proposition 3.4(2) these are the kernels from scale zero of an (S(d), rays)-cascade family.
At S = diag(sigma0) (positive definite) the kernel is delta_0.
Run: python3 delta_at_pd_family.py
"""
import numpy as np

rng = np.random.default_rng(20261103)


def sigma(S):
    ev = np.sort(np.linalg.eigvalsh(S))[::-1]
    return ev / ev.sum()


def make_phi(d, sigma0):
    c = np.full(d, 1.0 / d)

    def phi(s):
        a, b = np.linalg.norm(s - sigma0), np.linalg.norm(s - c)
        return a / (a + b)
    return phi


def C(S, phi):
    if np.allclose(S, 0):
        return np.zeros_like(S)
    return phi(sigma(S)) * np.trace(S) * np.eye(S.shape[0])


def rand_orth(d):
    Q, R = np.linalg.qr(rng.standard_normal((d, d)))
    return Q * np.sign(np.diag(R))


for d, sigma0 in ((2, np.array([0.7, 0.3])), (3, np.array([0.5, 0.3, 0.2]))):
    phi = make_phi(d, sigma0)
    print(f"d={d}, sigma0={sigma0}")
    print(f"  (a) C(0) = 0; C(I) = {np.diag(C(np.eye(d), phi))}")
    worst = 0.0
    for _ in range(3000):
        G = rng.standard_normal((d, rng.integers(1, d + 1)))
        S = G @ G.T
        c, Q = np.exp(rng.standard_normal()), rand_orth(d)
        A = c * Q
        worst = max(worst, np.abs(A @ C(S, phi) @ A.T - C(A @ S @ A.T, phi)).max()
                    / (1 + np.abs(C(S, phi)).max()))
    print(f"  (b) max relative |A C(S) A^T - C(A.S)| over similarities: {worst:.2e}")
    # (c) continuity: near 0, and along a path through an eigenvalue crossing and a singular matrix
    for t in (1e-2, 1e-4, 1e-8):
        S = t * np.diag(np.linspace(1, 0, d))
        print(f"  (c) |C(S)| at |S| ~ {t:g}: {np.abs(C(S, phi)).max():.2e}")
    path = [np.diag([1.0, s] + [0.5] * (d - 2)) for s in np.linspace(0, 2, 2001)]
    jumps = max(np.abs(C(path[i + 1], phi) - C(path[i], phi)).max() for i in range(2000))
    print(f"  (c) largest jump of C along diag(1, s, ...), s in [0,2], step 1e-3: {jumps:.2e}")
    S0 = np.diag(sigma0)
    print(f"  at the positive definite S = diag(sigma0): eigenvalues {np.linalg.eigvalsh(S0)},"
          f" C(S) = {np.abs(C(S0, phi)).max():.1e}, so nu_S = delta_0")
