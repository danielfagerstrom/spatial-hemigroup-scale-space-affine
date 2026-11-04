import numpy as np
from scipy import integrate, special
# d=2 -> target: shadow profile in R^2 of a radial Levy measure in R^3 equals the step b 1_(0,tau).
# Abel inverse gives k'(s) = (2b/pi) [arccos(s/tau) + s/sqrt(tau^2-s^2)] on (0,tau).
b, tau, d = 1.0, 1.0, 2
Cd = special.gamma((d+1)/2)/(np.sqrt(np.pi)*special.gamma(d/2))   # |S^{d-1}|/|S^d|
kp = lambda s: (2*b/np.pi)*(np.arccos(s/tau) + s/np.sqrt(tau**2 - s**2)) if s < tau else 0.0
def shadow(r):
    U = np.sqrt(tau**2/r**2 - 1)
    f = lambda u: kp(r*np.sqrt(1+u*u))*(1+u*u)**(-(d+1)/2)
    return Cd*integrate.quad(f, -U, U, limit=400)[0]
for r in (0.05, 0.3, 0.7, 0.95):
    print(f"d=2: r={r} shadow={shadow(r):.6f} target={b}")
print("Levy integrability in R^3:", integrate.quad(lambda s: min(s*s,1)*kp(s)/s, 0, tau)[0])
print("k'(0+) =", kp(1e-9), " (finite, = b)")
