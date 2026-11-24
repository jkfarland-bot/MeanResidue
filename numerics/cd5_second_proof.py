# Exact checks of the second proof of Theorem 1.1 (Section 6 of the note) and of the elementary bound
# for Delta(n) = (n - s(n))/2 - S_n (Section 5.3), independently of the Lean formalization.
#   rho_d(b)  = #{x mod d : x^2 = b mod d},   phi_d = sum_{e | d} mu(d/e) rho_e,
#   Lam_d(g)  = -(1/d) sum_{0<b<d} g(b) (b - d/2),   gamma(d) = Lam_d(phi_d).
# Class numbers are computed by counting reduced primitive forms, so no L-function is used.
import math, os
from fractions import Fraction as Fr
import numpy as np

N = int(os.environ.get('CD5_N', '2000'))        # range for root counts and gamma
NB = int(os.environ.get('CD5_NB', '20000'))     # range for the bound on Delta(n)

def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return sorted(ds)
def mu(n):
    f = factor(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)
def is_prime(n):
    return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))
def squarefree(n):
    return all(e == 1 for e in factor(n).values())

def jacobi(a, n):                    # n odd positive
    a %= n; t = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): t = -t
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: t = -t
        a %= n
    return t if n == 1 else 0
def kron(D, m):                      # Kronecker symbol (D/m), m >= 1
    if m == 1: return 1
    r = 1
    while m % 2 == 0:
        m //= 2
        if D % 2 == 0: return 0
        r *= 1 if D % 8 in (1, 7) else -1
    return r * (jacobi(D, m) if m > 1 else 1)
def chi4(b): return 0 if b % 2 == 0 else (1 if b % 4 == 1 else -1)
def chi8(b): return 0 if b % 2 == 0 else (1 if b % 8 in (1, 7) else -1)        # (8/b)
def chim8(b): return chi4(b) * chi8(b)                                          # (-8/b)

def hforms(D):
    h = 0; a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b - D) % 2: continue
            num = b * b - D
            if num % (4 * a): continue
            c = num // (4 * a)
            if c < a or (b < 0 and c == a): continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1: continue
            h += 1
        a += 1
    return h
def hstar(D):
    w = 6 if D == -3 else 4 if D == -4 else 2
    return Fr(2 * hforms(D), w)

fails = {}
def check(name, ok):
    fails.setdefault(name, [0, 0])
    fails[name][0] += 1
    if not ok: fails[name][1] += 1

# root counts rho_d as arrays indexed by b mod d
rho = {1: np.array([1], dtype=np.int64)}
for d in range(2, N + 1):
    r = np.zeros(d, dtype=np.int64)
    np.add.at(r, (np.arange(d, dtype=np.int64) ** 2) % d, 1)
    rho[d] = r
def tile(arr, d):
    return np.tile(arr, d // len(arr))
phi = {}
for d in range(1, N + 1):
    acc = np.zeros(d, dtype=np.int64)
    for e in divisors(d):
        m = mu(d // e)
        if m: acc += m * tile(rho[e], d)
    phi[d] = acc
def gamma(d):
    b = np.arange(d, dtype=np.int64)
    return Fr(-int((phi[d][1:] * (2 * b[1:] - d)).sum()), 2 * d)
G = {d: gamma(d) for d in range(1, N + 1)}

def S_exact(n):
    k = np.arange(n, dtype=np.int64)
    return Fr(int(((k * k) % n).sum()), n)
def s_of(n):
    r = 1
    for p, e in factor(n).items(): r *= p ** (e // 2)
    return r
def Delta(n):
    return Fr(n - s_of(n), 2) - S_exact(n)

# Lemma 6.1(a) and Proposition 6.2: Delta(n) = Lam_n(rho_n) = sum_{d | n} gamma(d)
for n in range(1, N + 1):
    b = np.arange(n, dtype=np.int64)
    lam = Fr(-int((rho[n][1:] * (2 * b[1:] - n)).sum()), 2 * n)
    D = Delta(n)
    check("6.1(a) Delta(n) = Lam_n(rho_n)", D == lam)
    check("6.2 Delta(n) = sum_{d|n} gamma(d)", D == sum((G[d] for d in divisors(n)), Fr(0)))
    check("rho_n(0) = s(n)", rho[n][0] == s_of(n))

# Lemma 6.3
for p in [q for q in range(2, N + 1) if is_prime(q)]:
    e = 0
    while p ** (e + 2) <= N:
        big, small = p ** (e + 2), p ** e
        check("6.3(a) rho_{p^(e+2)}(p^2 b) = p rho_{p^e}(b)",
              all(rho[big][(p * p * b) % big] == p * rho[small][b % small] for b in range(big)))
        e += 1
    if p > 2:
        check("6.3(b) phi_p = (b/p)", all(phi[p][b] == jacobi(b, p) for b in range(p)))
        if p * p <= N:
            nu = lambda b: p * (b % (p * p) == 0) - (b % p == 0)
            check("6.3(b) phi_{p^2} = nu_p", all(phi[p * p][b] == nu(b) for b in range(p * p)))
        e = 1
        while p ** (e + 2) <= N:
            big, small = p ** (e + 2), p ** e
            check("6.3(b) phi_{p^(e+2)}(b) = p[p^2|b] phi_{p^e}(b/p^2)",
                  all(phi[big][b] == (p * phi[small][(b // (p * p)) % small] if b % (p * p) == 0 else 0)
                      for b in range(big)))
            e += 1
check("6.3(c) phi_2 = 0", all(phi[2] == 0))
check("6.3(c) phi_4 = nu_2 + chi_-4",
      all(phi[4][b] == 2 * (b % 4 == 0) - (b % 2 == 0) + chi4(b) for b in range(4)))
check("6.3(c) phi_8 = chi_8 + chi_-8", all(phi[8][b] == chi8(b) + chim8(b) for b in range(8)))
e = 2
while 2 ** (e + 2) <= N:
    big, small = 2 ** (e + 2), 2 ** e
    check("6.3(c) phi_{2^(e+2)}(b) = 2[4|b] phi_{2^e}(b/4), e >= 2",
          all(phi[big][b] == (2 * phi[small][(b // 4) % small] if b % 4 == 0 else 0) for b in range(big)))
    e += 1

# Lemma 6.4: twist rule, parity and invariance under unit squares
for d in range(1, min(400, N + 1)):
    for x in range(1, 2 * d + 2):
        if math.gcd(x, d) != 1: continue
        ok = True
        for b in range(d):
            if d % 2 == 1 and phi[d][(x * b) % d] != jacobi(x, d) * phi[d][b]: ok = False
            if phi[d][(x * x * b) % d] != phi[d][b]: ok = False
        check("6.4 twist rule and unit squares", ok)
    if d % 2 == 1:
        check("6.4 parity", all(phi[d][(-b) % d] == jacobi(-1, d) * phi[d][b] for b in range(d)))

# Lemmas 6.5 and 6.6: the odd part of phi_c is an eigenfunction of b -> l b with eigenvalue (-c/l)
primes = [q for q in range(3, 200) if is_prime(q)]
for c in range(3, N + 1):
    if c % 4 not in (0, 3): continue
    od = [Fr(int(phi[c][b]) - int(phi[c][(-b) % c]), 2) for b in range(c)]
    for l in primes:
        if c % l == 0: continue
        lam = kron(-c, l)
        check("6.6 odd part twist (-c/l)", all(od[(l * b) % c] == lam * od[b] for b in range(c)))
    if c % 2 == 1:
        check("6.6 phi_c odd for c = 3 mod 4", all(od[b] == phi[c][b] for b in range(c)))
        check("6.6 phi_c(2b) = (-c/2) phi_c(b)",
              all(phi[c][(2 * b) % c] == kron(-c, 2) * phi[c][b] for b in range(c)))

# Proposition 6.8 and the conclusion gamma(c) = h*(-c)
def fundamental(c):
    if c % 4 == 3: return squarefree(c)
    if c % 4 == 0: return (c // 4) % 4 in (1, 2) and squarefree(c // 4)
    return False
def hK(c):
    return Fr(-sum(a * kron(-c, a) for a in range(1, c)), c)
for d in range(1, N + 1):
    if d % 4 in (1, 2):
        check("6.8(a) gamma = 0 on 1, 2 mod 4", G[d] == 0)
    else:
        if fundamental(d):
            check("6.8(b) gamma(c) = Bernoulli form at fundamental -c", G[d] == hK(d))
        for l in [q for q in range(2, N + 1) if is_prime(q) and q * q * d <= N]:
            check("6.8(c) gamma(l^2 c) = (l - (-c/l)) gamma(c)", G[l * l * d] == (l - kron(-d, l)) * G[d])
        check("Theorem 1.1, second proof: gamma(c) = h*(-c)", G[d] == hstar(-d))

# Proof of Proposition 5.3: Fourier coefficients of the sawtooth and Weyl differencing, for n <= 300
for n in range(2, 301):
    b = np.arange(n)
    saw = np.where(b == 0, 0.0, b / n - 0.5)
    for h in range(1, n):
        zeta = np.exp(-2j * np.pi * h / n)
        Fh = (saw * zeta ** b).sum()
        check("proof of 5.3: Fourier coefficient 1/(zeta-1) + 1/2", abs(Fh - (1 / (zeta - 1) + 0.5)) < 1e-9)
        check("proof of 5.3: |coefficient| <= n/(4 min(h, n-h))", abs(Fh) <= n / (4 * min(h, n - h)) + 1e-12)
        Gh = np.exp(2j * np.pi * h * (b * b % n) / n).sum()
        check("proof of 5.3: |G(h;n)|^2 <= n gcd(2h, n)", abs(Gh) ** 2 <= n * math.gcd(2 * h, n) + 1e-6)

# Proposition 5.3: Delta(n)^2 <= n^{3/2} (1 + log n)^3, for n <= NB
worst = (0.0, 0)
for n in range(1, NB + 1):
    D = Delta(n)
    bound = n ** 1.5 * (1 + math.log(n)) ** 3
    check("Proposition 5.3: Delta(n)^2 <= n^{3/2}(1 + log n)^3", float(D) ** 2 <= bound)
    if n > 1:
        r = abs(float(D)) / (n ** 0.75 * (1 + math.log(n)) ** 1.5)
        if r > worst[0]: worst = (r, n)

print(f"ranges: root counts and gamma for d <= {N}; bound for n <= {NB}")
for k, (tot, bad) in fails.items():
    print(f"{k}: {tot} checks, {bad} failures")
print(f"largest |Delta(n)| / (n^(3/4) (1 + log n)^(3/2)) for 2 <= n <= {NB}: {worst[0]:.4f} at n = {worst[1]}")
print("ALL OK" if all(bad == 0 for _, bad in fails.values()) else "FAILURES")
