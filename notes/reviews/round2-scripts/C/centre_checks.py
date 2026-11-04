"""Independent recomputation of the constants of section 3.3 / Appendix A.4 (part C)."""
import mpmath as mp
mp.mp.dps = 30
pi, euler, log, exp, gamma, digamma = mp.pi, mp.euler, mp.log, mp.exp, mp.gamma, mp.digamma

def S(d):      # |S^{d-1}|
    return 2 * pi**(mp.mpf(d)/2) / gamma(mp.mpf(d)/2)
def V(d):      # volume of unit ball
    return pi**(mp.mpf(d)/2) / gamma(mp.mpf(d)/2 + 1)
def R(d, c):   # Prop. 3.16(1)
    d, c = mp.mpf(d), mp.mpf(c)
    return gamma((d-c)/2) / (2**c * pi**(d/2) * gamma(c/2))
def kappa_closed(d):   # Lemma A.7(3)
    return (euler - digamma(mp.mpf(d)/2))/2 - log(2)
def Omega(d, t):       # sphere average of cos<xi,x>, t = |xi||x|
    d = mp.mpf(d)
    if t == 0: return mp.mpf(1)
    return gamma(d/2) * (2/t)**(d/2-1) * mp.besselj(d/2-1, t)

print("=== Lemma A.7: kappa_d, three independent routes ===")
for d in range(1, 7):
    # (i) closed form of the lemma
    kc = kappa_closed(d)
    # (ii) Mellin route: kappa_d = lim_{s->0} (M(s) - 1/s), M(s) = -Gamma(d/2) 2^{-1-s} Gamma(-s/2)/Gamma((d+s)/2)
    s = mp.mpf('1e-8')
    M = -gamma(mp.mpf(d)/2) * 2**(-1-s) * gamma(-s/2) / gamma((mp.mpf(d)+s)/2)
    km = M - 1/s
    # (iii) direct: int_0^rho (1-Omega_d(t)) dt/t - log rho, rho large, oscillatory tail by quadosc
    rho = mp.mpf(40)
    head = mp.quad(lambda t: (1-Omega(d, t))/t, [0, 1, 5, 10, 20, rho])
    # tail: - int_rho^inf Omega_d(t)/t dt  (converges; oscillatory)
    tail = -mp.quadosc(lambda t: Omega(d, t)/t, [rho, mp.inf], omega=1)
    kd = head + tail - log(rho)
    # (iv) lambda_d as the sphere mean of log|eta_1| via the Beta law of eta_1^2
    if d == 1:
        lam = mp.mpf(0)
    else:
        a, b = mp.mpf(1)/2, mp.mpf(d-1)/2
        lam = mp.quad(lambda u: u**(a-1)*(1-u)**(b-1)*log(u)/2, [0, 1]) / mp.beta(a, b)
    print(f"d={d}: closed {mp.nstr(kc,12)}  Mellin {mp.nstr(km,12)}  direct {mp.nstr(kd,10)}  lambda_d {mp.nstr(lam,12)} (closed lambda {mp.nstr(kc-euler,12)})")
print("kappa_1 - gammaE =", mp.nstr(kappa_closed(1)-euler, 10), "; kappa_2 - (gammaE - log2) =", mp.nstr(kappa_closed(2)-(euler-log(2)),10),
      "; kappa_3 - (gammaE - 1) =", mp.nstr(kappa_closed(3)-(euler-1),10))
for d in range(1,5):
    print(f"kappa_{d+2} - kappa_{d} + 1/{d} =", mp.nstr(kappa_closed(d+2)-kappa_closed(d)+mp.mpf(1)/d, 10))
print("psi(1/2) =", mp.nstr(digamma(mp.mpf(1)/2),12), " -gammaE-2log2 =", mp.nstr(-euler-2*log(2),12))

print("\n=== (A.2) bounds on Cin: Cin(X)-log X on [1, 1e4], and Cin(X)-log X >= -3 on (0,1) ===")
def Cin(X): return euler + log(X) - mp.ci(X)
vals = [Cin(mp.mpf(X)) - log(X) for X in [1,2,3,4,5,7,10,30,100,1000,10000]]
print("max Cin-logX on sample:", mp.nstr(max(vals),8), " min:", mp.nstr(min(vals),8), " (claimed within [-3, 13/4]); Cin(1) =", mp.nstr(Cin(1),8), "<= 1/4")

print("\n=== Example 3.14: Matern kernel, polar profile and constants ===")
def kpol(d, g, r):   # polar profile 4g/Gamma(d/2) (r/sqrt2)^{d/2} K_{d/2}(sqrt2 r)
    d = mp.mpf(d); r = mp.mpf(r)
    return 4*g/gamma(d/2) * (r/mp.sqrt(2))**(d/2) * mp.besselk(d/2, mp.sqrt(2)*r)
def kpol_from_34(d, g, r):  # (3.4) with k_I(u) = g e^{-u}
    d = mp.mpf(d); r = mp.mpf(r)
    return 2/gamma(d/2) * mp.quad(lambda v: v**(d/2-1)*exp(-v)*g*exp(-r**2/(2*v)), [0, mp.inf])
for d in (1,2,3):
    for r in (mp.mpf('0.3'), mp.mpf(1), mp.mpf(2)):
        print(f"  d={d} r={r}: closed {mp.nstr(kpol(d,mp.mpf(3)/4,r),10)}  via (3.4) {mp.nstr(kpol_from_34(d,mp.mpf(3)/4,r),10)}")
print("  d=1 check 2g e^{-sqrt2 r} at r=1:", mp.nstr(2*mp.mpf(3)/4*exp(-mp.sqrt(2)),10))
print("  d=3 check 2g(1+sqrt2 r)e^{-sqrt2 r} at r=1:", mp.nstr(2*mp.mpf(3)/4*(1+mp.sqrt(2))*exp(-mp.sqrt(2)),10))
print("  k_d(0+) (d=2, g=3/4), r=1e-6:", mp.nstr(kpol(2, mp.mpf(3)/4, mp.mpf('1e-6')),8), " expected 2g = 1.5")

def matern_consts(d, g):
    c = 2*g
    Ck = mp.quad(lambda r: kpol(d,g,r)/r, [1, mp.inf])
    I0 = mp.quad(lambda u: (c - kpol(d,g,u))/u, [0, mp.mpf('1e-3'), mp.mpf('0.1'), 1])
    K0 = exp(I0)
    A = exp(-Ck - c*kappa_closed(d))
    return c, Ck, K0, A
print("\n--- d=2, gamma=3/4 (the worked numbers of p. 25) ---")
c, Ck, K0, A = matern_consts(2, mp.mpf(3)/4)
Q = R(2, c) * A
coef = gamma(mp.mpf(2)/2 - mp.mpf(3)/4) / (2**(mp.mpf(3)/4) * pi * gamma(mp.mpf(3)/4))
print(f"C_k = {mp.nstr(Ck,6)} (paper 0.359);  K(0+) = {mp.nstr(K0,6)} (paper 2.023);  A = {mp.nstr(A,6)} (paper 0.831)")
print(f"R(2,3/2) = {mp.nstr(R(2,c),6)};  Q = {mp.nstr(Q,6)} (paper 0.277);  Q K(0+) = {mp.nstr(Q*K0,6)} (paper 0.560);  closed-form coefficient = {mp.nstr(coef,6)}")
print(f"A K(0+) = {mp.nstr(A*K0,8)}  vs 2^gamma = {mp.nstr(2**(mp.mpf(3)/4),8)}")
print("C_k closed form (3/2) K_0(sqrt2) =", mp.nstr(mp.mpf(3)/2*mp.besselk(0, mp.sqrt(2)),8))
print("--- A K(0+) = 2^gamma in every dimension (consistency of Lemma A.7 with the transform) ---")
for d in (1,2,3,4,5):
    for g in (mp.mpf(3)/4, mp.mpf('0.3'), mp.mpf('1.7')):
        c, Ck, K0, A = matern_consts(d, g)
        print(f"  d={d} gamma={g}: A K(0+) = {mp.nstr(A*K0,10)}   2^gamma = {mp.nstr(2**g,10)}")

print("\n--- the rate, Example 3.14 continued, gamma < d/2: p(x) ~ Gamma(d/2-g)/(2^g pi^{d/2} Gamma(g)) |x|^{2g-d} vs closed form (3.7) ---")
def p37(d, g, x):
    d = mp.mpf(d); x = mp.mpf(x)
    return 2/((2*pi)**(d/2)*gamma(g)) * (x/mp.sqrt(2))**(g-d/2) * mp.besselk(g-d/2, mp.sqrt(2)*x)
for d in (2,3):
    g = mp.mpf(3)/4
    for x in (mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-4')):
        asym = gamma(mp.mpf(d)/2-g)/(2**g*pi**(mp.mpf(d)/2)*gamma(g)) * x**(2*g-d)
        print(f"  d={d} |x|={x}: p={mp.nstr(p37(d,g,x),8)}  asym={mp.nstr(asym,8)}  ratio={mp.nstr(p37(d,g,x)/asym,8)}")
print("  d=1, gamma=3/4: p(0) = Gamma(1/4)/(sqrt(2 pi) Gamma(3/4)) =", mp.nstr(gamma(mp.mpf(1)/4)/(mp.sqrt(2*pi)*gamma(mp.mpf(3)/4)),8), " p(1e-4) =", mp.nstr(p37(1,mp.mpf(3)/4,mp.mpf('1e-4')),8))
print("  d=1 p(0) via Thm 3.12(3): (2pi)^{-1/2}/Gamma(1/2) int sigma^{-1/2}(1+sigma)^{-3/4} =",
      mp.nstr((2*pi)**(-mp.mpf(1)/2)/mp.sqrt(pi)*mp.quad(lambda s: s**(-mp.mpf(1)/2)*(1+s)**(-mp.mpf(3)/4), [0, mp.inf]),8))

print("\n--- threshold gamma = d/2: p(x) ~ 2 (2pi)^{-d/2} Gamma(d/2)^{-1} log(1/|x|); and B K(0+) of Prop. 3.17(3) ---")
for d in (1,2,3):
    g = mp.mpf(d)/2
    x = mp.mpf('1e-6')
    coefl = 2*(2*pi)**(-mp.mpf(d)/2)/gamma(mp.mpf(d)/2)
    print(f"  d={d}: p(1e-6)/log(1e6) = {mp.nstr(p37(d,g,x)/log(1/x),8)}  coef = {mp.nstr(coefl,8)}  (K_0 has a constant term: -gammaE+log(sqrt2) relative)")
    c, Ck, K0, A = matern_consts(d, g)
    B = (2*pi)**(-d) * S(d) * A
    print(f"       B K(0+) = {mp.nstr(B*K0,8)}  closed 2/(pi^(d/2)Gamma(d/2)) e^{{-C_k - d/2(gE-psi(d/2))}} K(0+) = {mp.nstr(2/(pi**(mp.mpf(d)/2)*gamma(mp.mpf(d)/2))*exp(-Ck-mp.mpf(d)/2*(euler-digamma(mp.mpf(d)/2)))*K0,8)}")

print("\n--- Q and B closed forms of p. 24 against R(d,c) A and (2pi)^{-d}|S^{d-1}| A, generic d, c, C_k ---")
for d in (2,3,5):
    for c in (mp.mpf('0.7'), mp.mpf(d)-mp.mpf('0.4')):
        Ck = mp.mpf('0.359')
        A = exp(-Ck - c*kappa_closed(d))
        Q1 = R(d,c)*A
        Q2 = gamma((mp.mpf(d)-c)/2)/(pi**(mp.mpf(d)/2)*gamma(c/2))*exp(-Ck - c/2*(euler-digamma(mp.mpf(d)/2)))
        print(f"  d={d} c={c}: Q(RA)={mp.nstr(Q1,12)}  Q(closed)={mp.nstr(Q2,12)}")
    A = exp(-mp.mpf('0.359') - d*kappa_closed(d))
    B1 = (2*pi)**(-d)*S(d)*A
    B2 = 2/(pi**(mp.mpf(d)/2)*gamma(mp.mpf(d)/2))*exp(-mp.mpf('0.359') - mp.mpf(d)/2*(euler-digamma(mp.mpf(d)/2)))
    print(f"  d={d}: B(closed via A)={mp.nstr(B1,12)}  B(closed form)={mp.nstr(B2,12)}")

print("\n--- R(d,c) against the Riesz kernel: (2pi)^{-d} int e^{-i<x,xi>}|xi|^{-c} dxi = R |x|^{c-d}, checked by Gaussian regularisation (d=2, c=3/2, d=3, c=1.2) ---")
# int_{R^d} |xi|^{-c} e^{-t|xi|^2/2} e^{-i x xi} dxi via polar + Omega; compare for small t
for d, c in ((2, mp.mpf(3)/2), (3, mp.mpf('1.2'))):
    x = mp.mpf(1); t = mp.mpf('1e-4')
    val = (2*pi)**(-d) * S(d) * mp.quad(lambda rho: rho**(d-1-c) * exp(-t*rho**2/2) * Omega(d, rho*x), [0, 1, 10, 50, 200, 800])
    print(f"  d={d} c={c}: regularised inverse transform at |x|=1: {mp.nstr(val,8)}   R(d,c) = {mp.nstr(R(d,c),8)}")

print("\n--- Prop. 3.16(2) lower-bound constant and the log profile example ---")
d = 2; c = mp.mpf(3)/2
print("  K(x) for k_d(u)=c(1-1/(2+log(1/u))) equals (1+log(1/x)/2)^c:  x=1e-3:",
      mp.nstr(exp(mp.quad(lambda u: (c/(2+log(1/u)))/u, [mp.mpf('1e-3'),1])),10), mp.nstr((1+log(1e3)/2)**c,10))

print("\n--- Prop. A.4 constants for d=2, c=3/2, gamma=3/4 Matern (eps_0 with k_d(eps_0) >= c/2) ---")
g = mp.mpf(3)/4
eps0 = mp.findroot(lambda r: kpol(2,g,r) - c/2, 1.0)
tau = min(mp.mpf(1)/2, mp.sqrt(mp.mpf(3)/(4*4*c)))
kappa0 = (c/(2*S(2)))**2 * V(2)/8**2
Ck = mp.quad(lambda r: kpol(2,g,r)/r, [1, mp.inf])
c1 = kappa0/4 * tau**c * exp(-Ck) * min(2**(c-2), 4**(c-2))
print(f"  eps_0={mp.nstr(eps0,6)} (any eps_0<= this works; take min(1,.)), tau={mp.nstr(tau,6)}, kappa_0={mp.nstr(kappa0,6)}, delta={mp.nstr(min(eps0,1)/2,6)}, c_1={mp.nstr(c1,6)}; actual coefficient Q K(0+)=0.560")
