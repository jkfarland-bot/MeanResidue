# Checks of the lemmas used in the proof, and of the extension of Conjecture 7.4 to all n.
import cmath, math
from cd_lib import *
def jacobi(a, n):            # n odd positive
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0
def kron(D, m):              # Kronecker symbol (D/m), m >= 1
    if m == 1: return 1
    r = 1
    while m % 2 == 0:
        m //= 2
        if D % 2 == 0: return 0
        r *= 1 if D % 8 in (1, 7) else -1
    return r * jacobi(D, m) if m > 1 else r
# (1) Gauss sums G(a;c) = sum_{k mod c} e(a k^2/c), gcd(a,c) = 1
bad = 0
for c in range(1, 301):
    for a in range(1, 2*c+1):
        if math.gcd(a, c) != 1: continue
        G = sum(cmath.exp(2j*math.pi*a*k*k/c) for k in range(c))
        if c % 2: pred = jacobi(a, c) * (1 if c % 4 == 1 else 1j) * math.sqrt(c)
        elif c % 4 == 2: pred = 0
        else: pred = (1 + 1j**a) * jacobi(c, a) * math.sqrt(c)
        bad += abs(G - pred) > 1e-7
print("(1) Gauss sum lemma, c <= 300, all a <= 2c prime to c: failures", bad)
# (2) characters: c = 3 mod 4: (a/c) = (-c/a); c = 0 mod 4, a odd: chi_{-4}(a)(c/a) = (-c/a)
bad = 0
for c in range(3, 2001):
    if c % 4 not in (0, 3): continue
    for a in range(1, 400):
        if math.gcd(a, c) != 1: continue
        if c % 4 == 3: bad += jacobi(a, c) != kron(-c, a)
        elif a % 2: bad += (1 if a % 4 == 1 else -1) * jacobi(c, a) != kron(-c, a)
print("(2) character identities, c <= 2000, a < 400: failures", bad)
# (3) class number formula h*(D) = (sqrt|D|/pi) sum (D/m)/m, by a smoothed partial sum (Cesaro over periods)
worst = 0
for c in [3, 4, 7, 8, 11, 12, 15, 16, 20, 23, 27, 28, 32, 36, 39, 44, 48, 63, 75, 99, 100, 108, 147, 175, 243, 400]:
    chi = [kron(-c, m) for m in range(1, c+1)]
    # L(1,chi) = -(1/c) sum_{a=1}^{c} chi(a) psi(a/c) for a character mod c; use sum over periods to 2e5 terms + tail bound
    Y = (200000 // c) * c
    L = sum(chi[(m-1) % c] / m for m in range(1, Y+1))
    val = math.sqrt(c)/math.pi*L
    worst = max(worst, abs(val - float(HS[c])))
print("(3) class number formula for orders, 26 discriminants incl. non-fundamental: max |error| %.1e (partial sums)" % worst)
# (4) Moebius form for all n: sum_{d|n} mu(n/d) ((d - s(d))/2 - S_d) = h*(-n) if n = 0,3 mod 4, else 0
def mu(n):
    f = factor(n); return 0 if any(e > 1 for e in f.values()) else (-1)**len(f)
Sd = {}
bad = 0; NM = 6000
for n in range(1, NM+1):
    Sd[n] = S_direct(n)
    v = sum((mu(n//d) * (Fr(d - s_of(d), 2) - Sd[d]) for d in divisors(n)), Fr(0))
    bad += v != (HS[n] if n % 4 in (0, 3) else 0)
print("(4) h*(-n)[n = 0,3 mod 4] = sum_{d|n} mu(n/d)((d - s(d))/2 - S_d), n <= %d: failures %d" % (NM, bad))
