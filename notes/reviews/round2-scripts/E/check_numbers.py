from mpmath import mp, gamma, pi, sqrt, quad, besselk, log, exp, euler, digamma, inf
mp.dps = 20
# Matern gamma=3/4, d=2: coefficient through the transform
g, d = mp.mpf(3)/4, 2
c = 2*g
R = gamma((d-c)/2)/(2**c*pi**(d/2)*gamma(c/2))
coef = 2**g*R
print("2^g R(d,2g) =", coef, " vs 2^-g pi^-d/2 G(d/2-g)/G(g) =", 2**(-g)*pi**(-d/2)*gamma(d/2-g)/gamma(g))
# polar profile k_d(r) = 4/Gamma(g) (r/sqrt2)^{d/2} ... K_{d/2}(sqrt2 r)? paper: k_d(r) = (4/Gamma(gamma)) (r/sqrt(2))^{d/2} ... K_{d/2}(sqrt2 r) times? check normalisation k_d(0+)=2g
def kd(r):
    return 4/gamma(g)*(r/sqrt(2))**(d/2)*besselk(d/2, sqrt(2)*r)  # guess; verify limit
print("kd(1e-6) ~", kd(mp.mpf('1e-6')), " expect c=", c)
# hmm, adjust: try general formula from (3.4): kd(r)= 2/Gamma(d/2) * int_0^inf v^{d/2-1} e^{-v} kI(r^2/(2v)) dv with kI(u)=g e^{-u}
def kd2(r):
    return 2/gamma(d/2)*quad(lambda v: v**(d/2-1)*exp(-v)*g*exp(-r**2/(2*v)), [0, inf])
print("kd2(1e-4)=", kd2(mp.mpf('1e-4')), "kd2(1)=", kd2(1), "kd(1)=", kd(1))
Ck = quad(lambda r: kd2(r)/r, [1, inf])
K0 = exp(quad(lambda u: (c-kd2(u))/u, [0,1]))
kap = (euler - digamma(mp.mpf(d)/2))/2 - log(2)
A = exp(-Ck - c*kap)
Q = R*A
print("Ck=",Ck," K(0+)=",K0," A=",A," Q=",Q," QK0=",Q*K0, " A*K0=", A*K0, " 2^g=", 2**g)
# w_d checks
for dd,w in [(2,5.24),(3,3.21)]:
    print(dd, w/sqrt(pi/dd))
