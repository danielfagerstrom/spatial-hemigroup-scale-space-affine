"""Blind check of claim (iii) from the definition, with no profile and no map.

F is in A_D exactly when F(|xi|), xi in R^D, is the exponent of a self-decomposable law: for every
lambda in (0,1) the residual  xi -> exp(-(F(|xi|) - F(lambda |xi|)))  is the characteristic
function of a law on R^D, so the matrix
    R_ij = exp(-(F(|xi_i - xi_j|) - F(lambda |xi_i - xi_j|)))
is positive semidefinite for every finite set of points of R^D. One point set with a negative
eigenvalue excludes F from A_D. (The converse is not a test: no finite search proves membership.
The searches in the dimension where membership holds are controls.)

Cases, F_phi(r) = int_0^r (1 - phi(u)) du/u  (c = 1):
  1. phi = J_0 = Omega_2      claim: in A_2, not in A_3
  2. phi = sin u/u = Omega_3  claim: in A_3 (and A_2), not in A_4
  3. phi = cos = Omega_1      claim: in A_1, not in A_2   (the Cin ray, Theorem 3.20)
  4. phi = (1 - u)_+ = h_1    claim: in A_1, not in A_2   (Gneiting's Euclid's hat at n = 1)

For each case and each dimension D the script searches point sets (random starts, Nelder-Mead on
the coordinates) for the smallest eigenvalue of R, at lambda = 0.9. A search that finds nothing
decides nothing: cases 2 (D = 4) and 4 (D = 2), where the violation is weak or needs many points,
are decided by c_filtration_bochner_test.py.

It also checks the profile the plane would need for case 4, k_2(s) = (1/s) int_0^s J_0: nonnegative,
not monotone, and with the exponent F_phi (r for r <= 1, 1 + log r for r >= 1).

Run: uv run --no-project --with mpmath --with scipy python c_filtration_residual_pd.py
"""
import numpy as np
from scipy import integrate, interpolate, optimize, special

RMAX = 400.0
GRID = np.linspace(0.0, RMAX, 400001)


def tabulate(phi, f0=0.0):
    """F(r) = int_0^r (1 - phi(u)) du/u: composite Simpson on a grid of step 5e-4, then a cubic
    spline through the values at the nodes of GRID (step 1e-3). The kink of the hat is at a node.
    f0 is the limit of (1 - phi(u))/u at 0: 0 for the smooth phi, 1 for the hat."""
    u = np.linspace(0.0, RMAX, 2 * (len(GRID) - 1) + 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        f = (1.0 - phi(u)) / u
    f[0] = f0
    h = u[1] - u[0]
    seg = h / 3.0 * (f[0:-2:2] + 4.0 * f[1:-1:2] + f[2::2])
    return interpolate.CubicSpline(GRID, np.concatenate(([0.0], np.cumsum(seg))))


def sinc(u):
    return np.sinc(u / np.pi)


CASES = [
    ("phi = J_0 (Omega_2)", special.j0, (2, 3), 0.0),
    ("phi = sin u/u (Omega_3)", sinc, (2, 3, 4), 0.0),
    ("phi = cos (Omega_1), the Cin ray", np.cos, (1, 2), 0.0),
    ("phi = (1-u)_+ (Euclid's hat h_1)", lambda u: np.clip(1.0 - u, 0.0, None), (1, 2), 1.0),
]
LAM = 0.9
THRESH = -1e-6  # the table of F is good to about 1e-11; rounding in eigvalsh to about 1e-15


def residual_min_eig(x, n, D, Ftab):
    P = x.reshape(n, D)
    dist = np.sqrt(((P[:, None, :] - P[None, :, :]) ** 2).sum(-1))
    if dist.max() >= RMAX:
        return 1.0
    g = Ftab(dist) - Ftab(LAM * dist)
    return np.linalg.eigvalsh(np.exp(-g))[0]


def search(Ftab, D, n, starts, rng, scale):
    best, bestx = np.inf, None
    for _ in range(starts):
        x0 = rng.normal(size=n * D) * scale
        res = optimize.minimize(residual_min_eig, x0, args=(n, D, Ftab), method="Nelder-Mead",
                                options={"maxiter": 6000, "maxfev": 6000, "xatol": 1e-7, "fatol": 1e-13})
        if res.fun < best:
            best, bestx = res.fun, res.x
    return best, bestx


def main():
    rng = np.random.default_rng(20261012)
    print(f"Residual matrices at lambda = {LAM}; n points in R^D; smallest eigenvalue found")
    print("(a negative value excludes F_phi from A_D; a value >= 0 is a control, not a proof)")
    for name, phi, dims, f0 in CASES:
        Ftab = tabulate(phi, f0)
        print(f"\n{name}:  F(1) = {float(Ftab(1.0)):.10f}, F(10) = {float(Ftab(10.0)):.10f}")
        for D in dims:
            out = []
            for n in (5, 7, 9):
                val, x = search(Ftab, D, n, starts=14, rng=rng, scale=4.0)
                out.append((val, n, x))
            val, n, x = min(out, key=lambda t: t[0])
            verdict = "NEGATIVE: not in A_%d" % D if val < THRESH else "no negative eigenvalue found"
            print(f"  D = {D}: min eigenvalue {val:+.3e} (n = {n})   {verdict}")
            if val < THRESH:
                P = x.reshape(n, D)
                # re-evaluate the witness set with direct quadrature of F, not the table
                dist = np.sqrt(((P[:, None, :] - P[None, :, :]) ** 2).sum(-1))

                def Fq(r):
                    if r == 0.0:
                        return 0.0
                    v, _ = integrate.quad(lambda u: (1.0 - phi(np.array(u))) / u if u > 0 else 0.0,
                                          0.0, r, limit=400, epsabs=1e-13, epsrel=1e-13)
                    return float(v)

                g = np.array([[Fq(dij) - Fq(LAM * dij) for dij in row] for row in dist])
                ev = np.linalg.eigvalsh(np.exp(-g))[0]
                print(f"         the same point set with F by direct quadrature: min eigenvalue {ev:+.3e}")
                print("         points:", np.array2string(P, precision=4, separator=", ").replace("\n", " "))
                assert ev < THRESH

    print("\nCase 4, the profile the plane would need: k_2(s) = (1/s) int_0^s J_0(u) du")
    k2 = lambda s: special.itj0y0(s)[0] / s
    s = np.linspace(0.01, 60.0, 6000)
    v = k2(s)
    dv = np.diff(v)
    print(f"  min k_2 on (0,60] = {v.min():.6f} (> 0);  k_2(0.01) = {v[0]:.6f};"
          f"  largest increase between grid points = {dv.max():.3e} at s = {s[np.argmax(dv)]:.3f}")
    inc = s[:-1][dv > 0]
    print(f"  k_2 increases on parts of ({inc.min():.2f}, {inc.max():.2f}); first interval of increase starts near"
          f" s = {inc.min():.3f}")
    assert v.min() > 0 and dv.max() > 0
    S = 4000.0
    for rho in (0.5, 1.0, 3.0):
        # int_0^S (1 - J_0(rho s)) k_2(s) ds/s, plus the tail  int_S^oo ~ 1/S
        val, _ = integrate.quad(lambda t: (1.0 - special.j0(rho * t)) * k2(t) / t if t > 0 else 0.0,
                                0.0, S, limit=200000, epsabs=1e-10, epsrel=1e-10)
        exact = rho if rho <= 1 else 1.0 + np.log(rho)
        print(f"  rho = {rho}: int_0^{S:.0f} (1 - J_0(rho s)) k_2(s) ds/s + 1/S = {val + 1.0 / S:.6f};"
              f"  F_phi(rho) = {exact:.6f}")
        assert abs(val + 1.0 / S - exact) < 2e-4
    print("  so F_phi(|xi|) with phi = h_1 is the exponent of an infinitely divisible law on the plane")
    print("  whose polar profile is not monotone: not self-decomposable there.")
    print("\ndone")


if __name__ == "__main__":
    main()
