"""Report B, part 3 (ii): continuity (K2) is needed in Theorem 3.6 only at the boundary of PSD(d).

The referee's family, for b > 0 and theta0 in [0, 1):
    mu_{S,S'} = N(0, 2b (theta(S') S' - theta(S) S)),  theta = 1 on PD(d), theta0 on singular S.
Checked on random pairs and triples of the Loewner order in PSD(d), d = 2, 3, singular ones
included (projections and rank-deficient Wisharts), with GL(d) maps:
  (P)  the covariance theta(S')S' - theta(S)S is PSD for every Loewner pair (so the laws exist);
  (K1) the covariances add along S <= S' <= S'' (transforms multiply), and vanish at S = S';
  (K3) A theta(S)S A^T = theta(ASA^T) ASA^T, since A in GL(d) preserves rank;
  (K4) mu_{0,I} = N(0, 2bI) is not delta_0;
  agreement with (3.1) on PD(d) pairs, disagreement at the singular ones (theta0 < 1);
  (K2) fails: hat mu_{0,diag(1,e,..)}(w) -> exp(-b w1^2), but hat mu_{0,diag(1,0,..)}(w)
       = exp(-b theta0 w1^2).
Run: python3 k2_boundary_family.py
"""
import numpy as np

rng = np.random.default_rng(20261103)
TOL = 1e-9


def theta(S, th0):
    return 1.0 if np.linalg.matrix_rank(S, tol=1e-10) == S.shape[0] else th0


def cov(S, Sp, b, th0):
    return 2 * b * (theta(Sp, th0) * Sp - theta(S, th0) * S)


def psd(M):
    return np.linalg.eigvalsh((M + M.T) / 2).min() >= -TOL


def rand_psd(d, rank):
    G = rng.standard_normal((d, rank))
    return G @ G.T


def loewner_chain(d):
    """S <= S' <= S'' with a random mixture of singular and definite members."""
    S = rand_psd(d, rng.integers(0, d + 1)) if rng.random() < 0.7 else np.zeros((d, d))
    Sp = S + rand_psd(d, rng.integers(0, d + 1))
    Spp = Sp + rand_psd(d, rng.integers(0, d + 1))
    return S, Sp, Spp


for d in (2, 3):
    b, th0 = 0.7, 0.3
    n_pairs = n_sing = 0
    worst_psd = worst_add = worst_cov = 0.0
    for _ in range(4000):
        S, Sp, Spp = loewner_chain(d)
        for (X, Y) in ((S, Sp), (Sp, Spp), (S, Spp)):
            n_pairs += 1
            n_sing += theta(X, th0) < 1 or theta(Y, th0) < 1
            worst_psd = min(worst_psd, np.linalg.eigvalsh(cov(X, Y, b, th0)).min())
        add = cov(S, Sp, b, th0) + cov(Sp, Spp, b, th0) - cov(S, Spp, b, th0)
        worst_add = max(worst_add, np.abs(add).max())
        A = rng.standard_normal((d, d))
        lhs = A @ cov(S, Sp, b, th0) @ A.T
        rhs = cov(A @ S @ A.T, A @ Sp @ A.T, b, th0)
        worst_cov = max(worst_cov, np.abs(lhs - rhs).max() / (1 + np.abs(lhs).max()))
    print(f"d={d}: {n_pairs} Loewner pairs ({n_sing} with a singular end)")
    print(f"  (P)  least eigenvalue of any increment covariance: {worst_psd:.2e} (>= -1e-9 is PSD)")
    print(f"  (K1) max |cov(S,S')+cov(S',S'')-cov(S,S'')|: {worst_add:.2e}")
    print(f"  (K3) max relative |A cov A^T - cov(A.S, A.S')|: {worst_cov:.2e}")
    I = np.eye(d)
    print(f"  (K4) cov(0, I) = {np.diag(cov(np.zeros((d, d)), I, b, th0))} (not 0)")
    # agreement with (3.1) on PD pairs, and at a singular pair
    S = rand_psd(d, d); Sp = S + rand_psd(d, d)
    print(f"  PD pair: |cov - 2b(S'-S)| = {np.abs(cov(S, Sp, b, th0) - 2*b*(Sp - S)).max():.2e}")
    P = np.diag([1.0] + [0.0] * (d - 1))
    print(f"  singular kernel from 0: cov(0,P)[0,0] = {cov(np.zeros((d, d)), P, b, th0)[0, 0]:.3f}"
          f" vs (3.1) {2*b:.3f}")
    # (K2) failure
    w = np.zeros(d); w[0] = 1.0
    for e in (1e-1, 1e-3, 1e-6):
        Se = np.diag([1.0] + [e] * (d - 1))
        v = np.exp(-0.5 * w @ cov(np.zeros((d, d)), Se, b, th0) @ w)
        print(f"  (K2) hat mu_(0,diag(1,{e:g},..))(e1) = {v:.6f}")
    v0 = np.exp(-0.5 * w @ cov(np.zeros((d, d)), P, b, th0) @ w)
    print(f"  (K2) hat mu_(0,diag(1,0,..))(e1)       = {v0:.6f}   (limit exp(-b) = {np.exp(-b):.6f})")
