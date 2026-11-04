"""Report B, part 2(b) and required change 1: does a rank-deficient step from a singular nonzero
base force the Gaussian?

For an orbit hat mu_S(w) = exp(-g(<w,S w>)), the increment of a step S -> S + P must have the
transform q(w) = exp(-g(<w,(S+P)w>) + g(<w,S w>)). If it is a probability measure, q = 1 on
ker P, and Lemma 3.8 makes q invariant under translation by ker P.

Case 1: S = e1 e1^T, P = I - e1 e1^T (Remark 3.13's step, read from the base e1e1^T).
  ker P = span(e1), and q(w1 e1 + w') = exp(-g(w1^2 + |w'|^2) + g(w1^2)). Invariance in w1
  is g(u + v) - g(u) = g(v) for u, v >= 0: Cauchy's equation, so g is linear (g >= 0).
  Checked numerically for the stable g(u) = u^(a/2): the dependence of q on w1 at fixed w'.
Case 2: S = e1 e1^T, P = e1 e1^T (a ray step, 0 < rank P < d): every self-decomposable orbit has
  a probability increment, the residual of self-decomposability at ratio 1/sqrt(2).
  Checked for the stable law: q(w) = exp(-(2^(a/2) - 1) |w1|^a), a 1-d stable transform.
Case 3: S = 0: q = hat mu_P, always a law.
Run: python3 singular_base_step.py
"""
import numpy as np

for a in (1.0, 1.5, 2.0):
    g = lambda u: u ** (a / 2)
    wp = 1.0  # |w'| fixed
    vals = [np.exp(-g(w1 ** 2 + wp ** 2) + g(w1 ** 2)) for w1 in (0.0, 0.5, 1.0, 2.0, 5.0)]
    spread = max(vals) - min(vals)
    print(f"stable index {a}: case 1, q(w1 e1 + e2) for w1 = 0, .5, 1, 2, 5:"
          f" {np.round(vals, 6)}; spread {spread:.3e}"
          f" ({'invariant: Gaussian' if spread < 1e-12 else 'not invariant: no probability increment'})")
    # case 2: ray step e1e1^T -> 2 e1e1^T
    w = np.array([0.7, -1.3])
    q = np.exp(-g(2 * w[0] ** 2) + g(w[0] ** 2))
    print(f"   case 2 (ray step): q(w) = {q:.6f} = exp(-(2^(a/2)-1)|w1|^a) ="
          f" {np.exp(-(2 ** (a / 2) - 1) * abs(w[0]) ** a):.6f}")
