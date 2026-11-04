r"""Item 11 of the round-2 presentation review: the formulas the proposed paragraph would put
into Section 4.6, checked against Remark E.3 and Proposition E.4 (Appendix E.2).

Checks
  (a) the would-be increment's transform: (1+<w,S w>)/(1+<w,S' w>) = 1 - <w,P w>/(1+<w,S' w>);
  (b) the constant B_d = (1/2) pi^{-d/2} Gamma(d/2) from the Newtonian leading term of the Green's
      function of 1 - Laplacian, for symbolic d, and that B_d = 1/|S^{d-1}|;
  (c) the exact limit r^d * div(P grad G)(r yhat) -> B_d (d <yhat,P yhat> - tr P) in d = 3
      (G = e^{-r}/(4 pi r)) and d = 2 (G = K_0(r)/(2 pi)), for a general symmetric P;
  (d) Proposition E.4(4): B_2 * Theta = (p1 - p2)/pi, and the step t^2 I -> t^2 diag(1+eps, 1).
Run: uv run --no-project --with sympy --with scipy python item11_matern_increment.py
"""
import sympy as sp

print("(a) transform identity")
u, up, pp = sp.symbols("u u_prime p", real=True)  # u = <w,Sw>, u' = <w,S'w> = u + p, p = <w,Pw>
lhs = (1 + u) / (1 + up)
rhs = 1 - pp / (1 + up)
print("   difference:", sp.simplify((lhs - rhs).subs(up, u + pp)))

print("(b) B_d from the Newtonian leading term, d symbolic")
d = sp.symbols("d", positive=True)
r = sp.symbols("r", positive=True)
# G(y) ~ c_d |y|^{2-d}, c_d = Gamma(d/2 - 1)/(4 pi^{d/2}) for d >= 3; Hessian of c r^{2-d}:
# c(2-d) r^{-d} (I - d yhat yhat^T), so tr(P' H) = c(d-2) r^{-d} (d<yhat,P'yhat> - tr P').
c_d = sp.gamma(d / 2 - 1) / (4 * sp.pi ** (d / 2))
B_from_G = sp.simplify(sp.gammasimp(c_d * (d - 2)))
B_paper = sp.Rational(1, 2) * sp.pi ** (-d / 2) * sp.gamma(d / 2)
sphere = 2 * sp.pi ** (d / 2) / sp.gamma(d / 2)
print("   c_d (d-2)            =", B_from_G)
print("   B_d (paper) - c_d(d-2) =", sp.simplify(sp.gammasimp(B_paper - B_from_G)))
print("   B_d * |S^{d-1}|      =", sp.simplify(B_paper * sphere))

print("(c) exact limits in d = 3 and d = 2")
x, y, z = sp.symbols("x y z", real=True)
a11, a22, a33, a12, a13, a23 = sp.symbols("a11 a22 a33 a12 a13 a23", real=True)


def div_P_grad(G, coords, P):
    grad = [sp.diff(G, c) for c in coords]
    return sum(sp.diff(sum(P[i][j] * grad[j] for j in range(len(coords))), coords[i])
               for i in range(len(coords)))


# d = 3
P3 = [[a11, a12, a13], [a12, a22, a23], [a13, a23, a33]]
R3 = sp.sqrt(x**2 + y**2 + z**2)
G3 = sp.exp(-R3) / (4 * sp.pi * R3)
q3 = div_P_grad(G3, (x, y, z), P3)
th, ph = sp.symbols("theta phi", real=True)
yhat = (sp.sin(th) * sp.cos(ph), sp.sin(th) * sp.sin(ph), sp.cos(th))
sub = {x: r * yhat[0], y: r * yhat[1], z: r * yhat[2]}
expr3 = sp.simplify(r**3 * q3.subs(sub))
lim3 = sp.simplify(sp.limit(expr3, r, 0))
quad3 = sum(P3[i][j] * yhat[i] * yhat[j] for i in range(3) for j in range(3))
target3 = B_paper.subs(d, 3) * (3 * quad3 - (a11 + a22 + a33))
print("   d=3: limit - B_3(3<yhat,P yhat> - tr P) =", sp.simplify(sp.trigsimp(lim3 - target3)))

# d = 2, numerically through K_0 (sympy's limit with besselk is slow; use mpmath)
import mpmath as mp

def q2_numeric(rr, phi, P):
    # G(y) = K_0(|y|)/(2 pi); radial: G' = -K_1/(2pi), G'' = (K_0 + K_1/r)/(2pi) (K_0'' identity)
    g1 = -mp.besselk(1, rr) / (2 * mp.pi)
    g2 = (mp.besselk(0, rr) + mp.besselk(1, rr) / rr) / (2 * mp.pi)
    e = (mp.cos(phi), mp.sin(phi))
    quad = sum(P[i][j] * e[i] * e[j] for i in range(2) for j in range(2))
    tr = P[0][0] + P[1][1]
    # Hessian of radial G: G'' e e^T + (G'/r)(I - e e^T)
    return g2 * quad + (g1 / rr) * (tr - quad)

P2 = [[0.7, 0.2], [0.2, 0.3]]
B2 = 1 / (2 * mp.pi)
worst = 0
for phi in [0.0, 0.4, 1.1, 2.0, 2.9]:
    e = (mp.cos(phi), mp.sin(phi))
    quad = sum(P2[i][j] * e[i] * e[j] for i in range(2) for j in range(2))
    target = B2 * (2 * quad - (P2[0][0] + P2[1][1]))
    val = mp.mpf(1e-8) ** 2 * q2_numeric(mp.mpf(1e-8), phi, P2)
    worst = max(worst, abs(val - target))
print("   d=2: max |r^2 q(r yhat) - B_2(2<yhat,P yhat> - tr P)| at r = 1e-8, 5 directions:",
      mp.nstr(worst, 3))

print("(d) Proposition E.4(4)")
p1, p2, phi, eps = sp.symbols("p1 p2 phi epsilon", positive=True)
bracket = 2 * (p1 * sp.cos(phi) ** 2 + p2 * sp.sin(phi) ** 2) - (p1 + p2)
print("   bracket in an eigenbasis:", sp.simplify(sp.trigsimp(bracket)))
# negative part of (p1-p2) cos 2 phi integrates over [0, 2pi] to 2(p1-p2)
neg = sp.integrate(-(p1 - p2) * sp.cos(2 * phi), (phi, sp.pi / 4, 3 * sp.pi / 4)) * 2
print("   integral of the negative part over the circle:", sp.simplify(neg))
print("   B_2 * Theta =", sp.simplify(B_paper.subs(d, 2) * neg))
Pp = sp.diag(eps / (1 + eps), 0)  # P' for Sigma = t^2 I, Sigma' = t^2 diag(1+eps,1)
print("   step t^2 I -> t^2 diag(1+eps,1): P' =", Pp, " B_2 Theta =",
      sp.simplify(B_paper.subs(d, 2) * 2 * (Pp[0, 0] - Pp[1, 1])))
print("(e) the bracket d<yhat,P'yhat> - tr P' has mean zero over the sphere and is negative at a")
print("    least eigenvector of P' unless P' is a multiple of I: d*lambda_min(P') < tr P' then.")
