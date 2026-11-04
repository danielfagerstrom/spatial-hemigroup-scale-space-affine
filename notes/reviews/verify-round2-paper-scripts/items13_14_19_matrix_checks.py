r"""Items 13, 14 and 19 of the round-2 presentation review: numerical checks of the matrix facts
that the proposed texts would put into the paper.

Item 13: a dilation x -> lam x acts on the parameter by Sigma -> lam^2 Sigma (A . Sigma = A Sigma A^T),
         t(Sigma) := det(Sigma)^{1/(2d)} is a length (t(lam^2 Sigma) = lam t(Sigma)), t(vI) = sqrt(v);
         under the slice of Prop. A.3(2), t(phi(t) I) = chi(t) with phi = chi^2.
Item 14: polar decomposition A = (A A^T)^{1/2} Q with Q orthogonal, and A, AQ' give the same A A^T.
Item 19: (i) Thm 4.3(1): along gamma(t) = S^{1/2} M^t S^{1/2}, gamma^{-1/2} gamma' gamma^{-1/2} is
         orthogonally conjugate to log M; (ii) log(M^{1/2} N M^{1/2}) != log M + log N when M, N do
         not commute (equality would force tr e^{X+Y} = tr e^X e^Y, the equality case of
         Golden-Thompson); (iii) Lemma C.1(2), the log-majorization l(M^{1/2} N M^{1/2}) < l(M) + l(N);
         (iv) Prop 4.2(3)'s example diag(4,1) then diag(4,1) or diag(1,4).
Run: python3 items13_14_19_matrix_checks.py   (numpy only)
"""
import numpy as np

rng = np.random.default_rng(20261103)


def spd(d):
    a = rng.standard_normal((d, d))
    return a @ a.T + 0.3 * np.eye(d)


def fn(S, f):
    w, v = np.linalg.eigh((S + S.T) / 2)
    return (v * f(w)) @ v.T


def sqrtm(S):
    return fn(S, np.sqrt)


def logm(S):
    return fn(S, np.log)


def isqrtm(S):
    return fn(S, lambda w: w ** -0.5)


def powm(S, t):
    return fn(S, lambda w: w ** t)


d = 3
print("Item 13")
S = spd(d)
lam = 1.7
A = lam * np.eye(d)
t = lambda Sig: np.linalg.det(Sig) ** (1 / (2 * d))
print("   A.Sigma - lam^2 Sigma:", np.abs(A @ S @ A.T - lam**2 * S).max())
print("   t(lam^2 Sigma)/t(Sigma) =", t(lam**2 * S) / t(S), " lam =", lam)
v = 2.3
print("   t(vI) - sqrt(v):", t(v * np.eye(d)) - np.sqrt(v))
chi = lambda s: 0.8 * s**1.3  # an arbitrary gauge
for s in (0.5, 1.0, 4.0):
    print(f"   s={s}: t(phi(s) I) - chi(s) = {t(chi(s) ** 2 * np.eye(d)) - chi(s):.2e}")

print("Item 14")
A = rng.standard_normal((d, d))
Sig = A @ A.T
Q = isqrtm(Sig) @ A
print("   |Q Q^T - I|:", np.abs(Q @ Q.T - np.eye(d)).max(),
      " |Sigma^{1/2} Q - A|:", np.abs(sqrtm(Sig) @ Q - A).max())
Qp, _ = np.linalg.qr(rng.standard_normal((d, d)))
print("   |(AQ')(AQ')^T - A A^T|:", np.abs((A @ Qp) @ (A @ Qp).T - Sig).max())

print("Item 19")
S = spd(d)
M = spd(d)
X = logm(M)
worst = 0.0
for tt in (0.2, 0.5, 0.9):
    g = sqrtm(S) @ powm(M, tt) @ sqrtm(S)
    h = 1e-6
    gp = (sqrtm(S) @ powm(M, tt + h) @ sqrtm(S) - sqrtm(S) @ powm(M, tt - h) @ sqrtm(S)) / (2 * h)
    Y = isqrtm(g) @ gp @ isqrtm(g)
    worst = max(worst, np.abs(np.sort(np.linalg.eigvalsh((Y + Y.T) / 2)) - np.sort(np.linalg.eigvalsh(X))).max())
print("   (i) geodesic velocity spectrum vs spectrum of log M, max diff:", f"{worst:.2e}")
N = spd(d)
P = sqrtm(M) @ N @ sqrtm(M)
comm = np.abs(M @ N - N @ M).max()
print(f"   (ii) |MN - NM| = {comm:.3f}; |log(M^1/2 N M^1/2) - log M - log N| =",
      f"{np.abs(logm(P) - logm(M) - logm(N)).max():.3f}")
Xc, Yc = logm(M), logm(N)
print("        tr e^{X+Y} =", f"{np.trace(fn(Xc + Yc, np.exp)):.4f}", " tr e^X e^Y =",
      f"{np.trace(fn(Xc, np.exp) @ fn(Yc, np.exp)):.4f}")
Mc = fn(np.diag([1.0, 2.0, 3.0]), lambda w: w)
Nc = np.diag([0.5, 4.0, 1.5])
print("        commuting pair: |log(M^1/2 N M^1/2) - log M - log N| =",
      f"{np.abs(logm(sqrtm(Mc) @ Nc @ sqrtm(Mc)) - logm(Mc) - logm(Nc)).max():.2e}")
viol = 0.0
for _ in range(2000):
    M, N = spd(d), spd(d)
    lp = np.sort(np.log(np.linalg.eigvalsh(sqrtm(M) @ N @ sqrtm(M))))
    ls = np.sort(np.log(np.linalg.eigvalsh(M))) + np.sort(np.log(np.linalg.eigvalsh(N)))
    for k in range(1, d):
        viol = max(viol, np.cumsum(ls)[k - 1] - np.cumsum(lp)[k - 1])  # need s_k(lp) >= s_k(ls)
    viol = max(viol, abs(lp.sum() - ls.sum()))
print("   (iii) Lemma C.1(2) over 2000 random pairs: largest violation", f"{viol:.2e}", "(<= 0 or rounding)")
D41, D14 = np.diag([4.0, 1.0]), np.diag([1.0, 4.0])
print("   (iv) diag(4,1) then diag(4,1):", np.diag(sqrtm(D41) @ D41 @ sqrtm(D41)),
      " then diag(1,4):", np.diag(sqrtm(D41) @ D14 @ sqrtm(D41)))
