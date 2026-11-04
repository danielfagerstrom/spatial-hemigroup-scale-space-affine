# /// script
# dependencies = ["numpy"]
# ///
"""Round 3, reports C and D: three small checks on the orders of sections 4.4 and 4.6.

(a) Report D, item 2 (p. 41): is the union over alpha of the exponent cones k_alpha,
    (d + alpha) lambda_min(sym B) >= tr B, the Gaussian's cone {sym B >= 0}?
    B = diag(1, 0) has sym B >= 0, and is an exponent of N(0, I): (e^{-tB})_* N(0, I) =
    N(0, diag(e^{-2t}, 1)), and N(0, I) = N(0, diag(e^{-2t}, 1)) * N(0, diag(1 - e^{-2t}, 0)).
    It lies in no k_alpha. Its perturbation B + eta I lies in k_alpha for alpha large.

(b) Report D, item 5 (Proposition 4.13, "the ordered-density cone"): is the step set
    K_R = {M : lambda_min(M) >= 1, det M <= lambda_min(M)^d R(lambda_min(M)^{1/2})^2}
    closed under M -> M^{1/2}?  The dyadic profile of Lemma 4.14(5), k(r) = 2^n on
    (2^{-n-1}, 2^{-n}], has R = 1 on [1, 2) and R(2) = 2. M = diag(4, ..., 4, 16) is in K_R
    (on its boundary); M^{1/2} = diag(2, ..., 2, 4) is not. So K_R is exp C for no cone C
    (a set exp C is closed under M -> M^tau, 0 <= tau <= 1).

(c) Report C, suggestion 1 (proof of Proposition 4.15): Lambda(phi) = lim_{R -> 0} int phi(x/R) rho(dx)
    equals rho({0}) phi(0) by dominated convergence, so h == rho({0}) and, for the ray Sigma' = c Sigma,
    rho({0}) = c^{-kappa}. For the Matern orbit (kappa = gamma, c = lam^2) this is lam^{-2 gamma},
    the probability of no jump of the compound Poisson residual of Proposition 4.4(4), whose Levy
    measure has mass 2 gamma log lam (Frullani). Checked numerically for two parameter pairs.

Run: python3 records/affine/reviews/verify-round3-paper-scripts/orders_checks.py
"""
import numpy as np


def in_k(B, alpha):
    S = 0.5 * (B + B.T)
    return (len(B) + alpha) * np.linalg.eigvalsh(S).min() >= np.trace(B) - 1e-12


def dyadic_k(r):
    n = np.ceil(-np.log2(r)) - 1  # r in (2^{-n-1}, 2^{-n}]
    return 2.0 ** n


def dyadic_R(lam, rs=np.exp(np.linspace(np.log(1e-6), np.log(1e3), 200001))):
    return np.min(dyadic_k(rs / lam) / dyadic_k(rs))


def in_KR(M, R):
    ev = np.linalg.eigvalsh(M)
    lmin = ev.min()
    return lmin >= 1 - 1e-12 and np.prod(ev) <= lmin ** len(ev) * R(np.sqrt(lmin)) ** 2 * (1 + 1e-9)


def main():
    print("(a) union of the exponent cones")
    B = np.diag([1.0, 0.0])
    print("  B = diag(1,0): in k_alpha for alpha in {1, 10, 1e3, 1e6}?",
          [in_k(B, a) for a in [1, 10, 1e3, 1e6]])
    for eta in [1e-1, 1e-3]:
        a_needed = (np.trace(B) + 2 * eta) / (eta) - 2  # (2 + a) eta >= 1 + 2 eta
        print(f"  B + {eta:g} I in k_alpha from alpha = {a_needed:.1f}:",
              in_k(B + eta * np.eye(2), a_needed + 1e-9), "(so the closure of the union is {sym B >= 0})")
    t = 0.7
    cov_res = np.eye(2) - np.diag([np.exp(-2 * t), 1.0])
    print("  residual covariance of N(0,I) for B = diag(1,0), t = 0.7:", np.diag(cov_res),
          "PSD:", np.all(np.linalg.eigvalsh(cov_res) >= -1e-15))

    print("\n(b) ordered-density step set of the dyadic profile, d = 2 and d = 3")
    print(f"  R(sqrt 2) = {dyadic_R(np.sqrt(2)):.6f}, R(2) = {dyadic_R(2.0):.6f}, R(1.9) = {dyadic_R(1.9):.6f}")
    for d in [2, 3]:
        M = np.diag([4.0] * (d - 1) + [16.0])
        Mh = np.diag([2.0] * (d - 1) + [4.0])
        print(f"  d = {d}: M = diag(4,...,4,16) in K_R: {in_KR(M, dyadic_R)};"
              f"  M^(1/2) = diag(2,...,2,4) in K_R: {in_KR(Mh, dyadic_R)}")

    print("\n(c) the atom of a Matern ray increment")
    for gamma, lam in [(1.0, 1.5), (2.5, 1.2)]:
        # Proposition 4.4(4): E e^{-uY} = ((1+u)/(1+lam^2 u))^gamma; P(Y = 0) = lim_{u->inf}
        u = 1e12
        atom_lt = ((1 + u) / (1 + lam**2 * u)) ** gamma
        # compound Poisson: Levy measure gamma (e^{-x/lam^2} - e^{-x}) x^{-1} dx, mass 2 gamma log lam
        x = np.exp(np.linspace(np.log(1e-12), np.log(200.0), 2_000_001))
        dens = gamma * (np.exp(-x / lam**2) - np.exp(-x)) / x
        mass = np.trapezoid(dens * x, np.log(x))
        print(f"  gamma = {gamma}, lam = {lam}: lam^(-2 gamma) = {lam**(-2*gamma):.6f}, "
              f"lim_u E e^(-uY) = {atom_lt:.6f}, e^(-Levy mass) = {np.exp(-mass):.6f} "
              f"(mass {mass:.6f} vs 2 gamma log lam = {2*gamma*np.log(lam):.6f})")


if __name__ == "__main__":
    main()
