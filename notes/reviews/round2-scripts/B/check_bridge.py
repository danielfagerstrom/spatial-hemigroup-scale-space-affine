"""Numerical checks for referee part B (Proposition 3.11 and (3.4))."""
import mpmath as mp

mp.mp.dps = 30

# Prop 3.11(4): E exp(-T_1 w^2/2) with T_1 ~ u^{-v-1} e^{-1/(2u)} / (2^v Gamma(v))
def student_transform(v, w):
    f = lambda u: u**(-v-1)*mp.e**(-1/(2*u) - u*w**2/2) / (2**v*mp.gamma(v))
    return mp.quad(f, [0, 1, mp.inf])

for v in (mp.mpf('0.5'), mp.mpf('1.5'), mp.mpf('3')):
    for w in (mp.mpf('0.7'), mp.mpf('2.3')):
        lhs = student_transform(v, w)
        rhs = 2**(1-v)/mp.gamma(v) * w**v * mp.besselk(v, w)
        print('Student-t  v=%s w=%s  mixture=%s  closed=%s  diff=%.2e' % (v, w, mp.nstr(lhs, 12), mp.nstr(rhs, 12), float(abs(lhs-rhs))))

# (3.4) with the gamma delay profile k_I(u) = g e^{-u}, at d = 1, against 2 g e^{-sqrt2 r}
def polar_profile(d, kI, r):
    f = lambda v: v**(d/mp.mpf(2)-1)*mp.e**(-v)*kI(r**2/(2*v))
    return 2/mp.gamma(d/mp.mpf(2)) * mp.quad(f, [0, 1, mp.inf])

g = mp.mpf('1.3')
kI = lambda u: g*mp.e**(-u)
for r in (mp.mpf('0.2'), mp.mpf('1'), mp.mpf('2.5')):
    k1 = polar_profile(1, kI, r)
    print('(3.4) d=1 gamma delay r=%s  k_1=%s  2g e^{-sqrt2 r}=%s' % (r, mp.nstr(k1, 12), mp.nstr(2*g*mp.e**(-mp.sqrt(2)*r), 12)))

# Matern exponent identity of Prop 3.11(2): F_I(r^2/2) with F_I = g log(1+s)
r = mp.mpf('1.7')
print('Matern exponent', g*mp.log(1+r**2/2), '== transform -log (1+r^2/2)^{-g}:', -mp.log((1+r**2/2)**(-g)))
