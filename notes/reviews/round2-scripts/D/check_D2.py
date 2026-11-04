import mpmath as mp, numpy as np
from scipy import integrate, special, optimize
mp.mp.dps = 40
def w(d):
    m = mp.mpf(d+1)/2; lam = mp.mpf(2)**(-mp.mpf(d)/2)
    h = lambda z: mp.exp(m*mp.log(z) - z) - lam*mp.exp(m*mp.log(z) - z/2)
    res = optimize.minimize_scalar(lambda z: -float(h(mp.mpf(z))), bounds=(1e-9, float(d*np.log(2))), method="bounded", options={"xatol":1e-13})
    return mp.gamma(m)/(2*h(mp.mpf(res.x)))
vals = {d: float(mp.sqrt(d)*w(d)) for d in range(200, 301)}
print("sqrt(d) w_d at 200, 250, 300:", vals[200], vals[250], vals[300])
print("nondecreasing on 200..300:", all(vals[d] <= vals[d+1] for d in range(200, 300)))
# A.19 sanity against (3.4)
d, wv, r = 3, 4.0, 1.5
kI = lambda u: u**-0.5 + wv*(1 <= u <= 2)
f = lambda v: v**(d/2-1)*np.exp(-v)*kI(r*r/(2*v))
a, b = r*r/4, r*r/2
direct = 2/special.gamma(d/2)*(integrate.quad(f, 0, a)[0] + integrate.quad(f, a, b)[0] + integrate.quad(f, b, np.inf)[0])
A19 = (2**1.5*special.gamma((d+1)/2)/special.gamma(d/2))/r + 2*wv*(special.gammainc(d/2, r*r/2) - special.gammainc(d/2, r*r/4))
print("direct (3.4) =", direct, " (A.19) =", A19)
