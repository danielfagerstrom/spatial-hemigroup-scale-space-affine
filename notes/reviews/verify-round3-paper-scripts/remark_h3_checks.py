#!/usr/bin/env python3
"""Round-3 verification (report E, section 4): Remark H.3 re-run and the referee's further claims.

Uses the deposited script's increment() (records/affine/check-gaussian-matern-step.py) unchanged,
for the plane, Sigma = diag(1, 0.3), P = diag(0.05, 0.55), kappa = 2, Matern index 1, C = 2b Sigma.
Checks: (1) the remark's two values at b = 2 and b = 0.1 at 1024^2 and 2048^2 (and 4096^2);
(2) the referee's ray calibration Sigma -> 1.4 Sigma at b = 0.1, n = 1024 and 2048;
(3) the size of the Gaussian factor at the 1024 grid's largest frequency along omega_1;
(4) the referee's sub-steps along the segment Sigma + tau P at b = 2;
(5) the referee's threshold between b = 0.3 and b = 0.5 for the full step.
Run from the repository root: python3 records/affine/reviews/verify-round3-paper-scripts/remark_h3_checks.py
"""
import importlib.util, pathlib
import numpy as np

spec = importlib.util.spec_from_file_location(
    "h3", pathlib.Path("records/affine/check-gaussian-matern-step.py"))
h3 = importlib.util.module_from_spec(spec); spec.loader.exec_module(h3)
inc = h3.increment

S = np.diag([1.0, 0.3]); P = np.diag([0.05, 0.55]); kappa = 2.0
H2 = h3.h(S + P, kappa)
print("h(Sigma) =", np.diag(h3.h(S, kappa)), " h(Sigma') =", np.diag(H2),
      " side 60*sqrt(lmax h(Sigma')) =", round(60 * np.sqrt(H2.max()), 2))
for n in (1024, 2048):
    L = 60 * np.sqrt(H2.max()); dx = L / n
    print(f"n = {n}: spatial spacing {dx:.4f}, largest frequency pi/dx = {np.pi/dx:.2f}")

print("\n(1) the remark's step")
for b in (2.0, 0.1):
    for n in (1024, 2048, 4096):
        r, neg, where = inc(S, P, b, kappa, n=n)
        print(f"  b = {b}, n = {n}: min/max {r:+.2e}, negative mass {neg:.2e}")

print("\n(2) ray calibration Sigma -> c Sigma")
for c in (1.4, 2.0):
    for b in (0.1, 2.0):
        for n in (1024, 2048):
            r, neg, _ = inc(S, (c - 1) * S, b, kappa, n=n)
            print(f"  c = {c}, b = {b}, n = {n}: min/max {r:+.2e}, negative mass {neg:.2e}")

print("\n(3) Gaussian factor exp(-b P11 w1^2) at the largest frequency, b = 0.1")
for n in (1024, 2048):
    L = 60 * np.sqrt(H2.max()); wmax = np.pi / (L / n)
    print(f"  n = {n}: w1 = {wmax:.2f}, factor {np.exp(-0.1*0.05*wmax**2):.3g}")

print("\n(4) sub-steps Sigma + tau0 P -> Sigma + tau1 P at b = 2 (Gaussian part 2b times the segment)")
for t0, t1 in ((0, 0.5), (0.5, 1), (0, 0.25), (0, 0.1), (0, 0.02)):
    for n in (1024, 2048):
        r, neg, _ = inc(S + t0 * P, (t1 - t0) * P, 2.0, kappa, n=n)
        print(f"  tau {t0} -> {t1}, n = {n}: min/max {r:+.2e}, negative mass {neg:.2e}")

print("\n(5) full step, b between 0.1 and 2")
for b in (0.2, 0.3, 0.4, 0.5, 1.0):
    r, neg, _ = inc(S, P, b, kappa, n=2048)
    print(f"  b = {b}: min/max {r:+.2e}, negative mass {neg:.2e}")
