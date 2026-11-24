# Exact check of the closed formulas for S_n and f(n) (Chamberland-Dilcher, arXiv 2510.04387, Section 7).
#   S_n  = (1/n) sum_{k=1}^{n-1} Rem(k^2 / n) = sum_{k mod n} {k^2/n}
#   f(n) = sum_{j<=floor(n/4)} floor(sqrt(jn)) - (n^2-1)/12
# Claims:  S_n = (n - s(n))/2 - T(n),  s(n) = prod p^floor(v_p(n)/2),  T(n) = sum_{c | n, c = 0,3 mod 4} h*(-c),
#          h*(D) = 2 h(D)/w(D), h(D) = number of classes of primitive positive definite forms of discriminant D.
#          f(n) = (s-1)/4 - T/2 (n=1 mod 4), (s-n)/4 - T/2 (n=3), n/8 + s/4 - T/2 (n=0), -n/8 + (s-1)/4 - T/2 (n=2).
# Class numbers are computed by counting reduced forms, independently of any L-function formula.
import sys, math
from fractions import Fraction as Fr
import numpy as np
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

def hforms(D):          # D < 0, D = 0,1 mod 4: number of reduced primitive forms
    h = 0; a = 1
    while 3*a*a <= -D:
        for b in range(-a+1, a+1):
            if (b - D) % 2: continue
            num = b*b - D
            if num % (4*a): continue
            c = num // (4*a)
            if c < a: continue
            if b < 0 and c == a: continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1: continue
            h += 1
        a += 1
    return h
def hstar(D):
    w = 6 if D == -3 else 4 if D == -4 else 2
    return Fr(2*hforms(D), w)

HS = {c: hstar(-c) for c in range(3, NMAX+1) if c % 4 in (0, 3)}
print("class numbers computed for", len(HS), "discriminants; h*(-3), h*(-4), h*(-12), h*(-15), h*(-23) =",
      HS[3], HS[4], HS[12], HS[15], HS[23])

def factor(n):
    f = {}; d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d*p**k for d in ds for k in range(e+1)]
    return ds
def s_of(n):
    r = 1
    for p, e in factor(n).items(): r *= p**(e//2)
    return r
def T_of(n):
    return sum((HS[c] for c in divisors(n) if c % 4 in (0, 3)), Fr(0))

def isqrt_arr(x):
    r = np.floor(np.sqrt(x.astype(np.float64))).astype(np.int64)
    r -= (r*r > x); r += ((r+1)*(r+1) <= x)
    return r

badS = badf = 0; firstbad = []
for n in range(1, NMAX+1):
    k = np.arange(1, n, dtype=np.int64)
    Sn = Fr(int(np.sum(k*k % n)), n) if n > 1 else Fr(0)
    J = n // 4; j = np.arange(1, J+1, dtype=np.int64)
    fn = Fr(int(isqrt_arr(j*n).sum())) - Fr(n*n - 1, 12)
    s = s_of(n); T = T_of(n)
    if Sn != Fr(n - s, 2) - T:
        badS += 1; firstbad.append(('S', n))
    r = n % 4
    pred = {1: Fr(s-1, 4), 3: Fr(s-n, 4), 0: Fr(n, 8) + Fr(s, 4), 2: Fr(-n, 8) + Fr(s-1, 4)}[r] - T/2
    if fn != pred:
        badf += 1; firstbad.append(('f', n))
print("n <= %d: S_n formula failures %d, f(n) formula failures %d %s" % (NMAX, badS, badf, firstbad[:5]))
