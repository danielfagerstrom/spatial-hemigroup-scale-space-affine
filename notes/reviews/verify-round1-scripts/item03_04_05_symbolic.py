"""VERIFY round 1, items 3, 4 and 5: three symbolic checks.

Item 3. The stable exponents of prop:isotropic-bridge(3) are F(r) = 2^(-alpha) r^(2 alpha),
0 < alpha <= 1. By cor:origin-profile-exponent, a = lim 2 F(r)/r^2 and
c = lim (F(r) - a r^2/2)/log r. For alpha < 1: a = 0 and c = infinity. For alpha = 1 (the
Gaussian): a = 1 and c = 0.

Item 4. The hypothesis of C6 (thm:cited-A10) at d = 0 and at d = 1. On R^0 = {0} every point is
0, so the form is f(0) |sum c_j|^2 and the hypothesis says f(0) >= 0. On R^1 with n = 1,
xi_1 = 0, c_1 = 1 the form is f(0) + f(0) - f(0) = f(0). So the hypothesis at d = 1 implies the
hypothesis at d = 0.

Item 5. The identity behind the uniqueness of a Bernstein triplet
(blueprint lem:bernstein-triplet-unique):
  (1 - e^(-s t)) + (1 - e^(-(s+2) t)) + e^(-s t) (1 - e^(-t))^2 = 2 (1 - e^(-(s+1) t)),
so G(s) + G(s+2) + int e^(-s t) (1 - e^(-t))^2 m(dt) = 2 G(s+1) for
G(s) = a + b s + int (1 - e^(-s t)) m(dt).

Run: uv run --no-project --with sympy python item03_04_05_symbolic.py
"""
import sympy as sp

r, s, t = sp.symbols("r s t", positive=True)

print("Item 3")
for alpha in (sp.Rational(1, 4), sp.Rational(1, 2), sp.Rational(9, 10), sp.Integer(1)):
    F = 2 ** (-alpha) * r ** (2 * alpha)
    a = sp.limit(2 * F / r ** 2, r, sp.oo)
    c = sp.limit((F - a * r ** 2 / 2) / sp.log(r), r, sp.oo)
    print(f"  alpha = {alpha}: a = {a}, c = {c}")
    assert (alpha < 1 and a == 0 and c == sp.oo) or (alpha == 1 and a == 1 and c == 0)

print("Item 4")
f0 = sp.Symbol("f0", real=True)
n = 3
cs = sp.symbols("c1:%d" % (n + 1))
form0 = sum((f0 + f0 - f0) * cj * sp.conjugate(ck) for cj in cs for ck in cs)
total = sum(cs)
assert sp.simplify(sp.expand(form0 - f0 * total * sp.conjugate(total))) == 0
print("  on R^0 the form with n = 3 is f(0) |c1 + c2 + c3|^2:  True")
print("  on R^1 with n = 1, xi_1 = 0, c_1 = 1 the form is f(0) + f(0) - f(0) =", sp.simplify(f0 + f0 - f0))

print("Item 5")
lhs = (1 - sp.exp(-s * t)) + (1 - sp.exp(-(s + 2) * t)) + sp.exp(-s * t) * (1 - sp.exp(-t)) ** 2
rhs = 2 * (1 - sp.exp(-(s + 1) * t))
assert sp.simplify(sp.expand(lhs - rhs)) == 0
print("  the second-difference identity holds:  True")
