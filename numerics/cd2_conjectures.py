# Conjectures 7.1-7.5 of Chamberland-Dilcher (arXiv 2510.04387) as printed, against direct computation.
from cd_lib import *
def leg(a, p): return 0 if a % p == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)
def g(p, e): return Fr(p**e - 1, p - 1)          # 1 + p + ... + p^{e-1}
P1 = [p for p in range(5, 200) if all(p % d for d in range(2, p)) and p % 4 == 1]
P3 = [p for p in range(3, 200) if all(p % d for d in range(2, p)) and p % 4 == 3]
# 7.1: n = p^a q^b, p = 1, q = 3 (mod 4)
cnt = okp = okm = 0
for p in P1:
    for q in P3:
        for a in range(1, 6):
            for b in range(1, 6):
                n = p**a * q**b
                if n > NMAX: continue
                cnt += 1; S = S_direct(n)
                base = Fr(n - p**(a//2) * q**(b//2), 2)
                X = g(q, (b+1)//2) * ((g(p, (a+2)//2) - g(p, a//2) * leg(p, q)) * HS[q])
                Y = g(q, (b+1)//2) * g(p, (a+1)//2) * HS[p*q]
                okm += S == base - (X - Y)      # sign as transcribed: ... h*(-q) - (...) h*(-pq)
                okp += S == base - (X + Y)      # sign + for the h*(-pq) term
print("7.1: %d values n = p^a q^b <= %d; holds with '-(...)h*(-pq)' inside: %d, with '+': %d" % (cnt, NMAX, okm, okp))
# 7.2: p, q = 3 (mod 4)
cnt = ok = 0
for i, p in enumerate(P3):
    for q in P3[i+1:]:
        for a in range(1, 6):
            for b in range(1, 6):
                n = p**a * q**b
                if n > NMAX: continue
                cnt += 1
                pred = Fr(n - p**(a//2) * q**(b//2), 2) \
                    - (g(q, b//2) * leg(p, q) + g(q, b//2 + 1)) * g(p, (a+1)//2) * HS[p] \
                    - (g(p, a//2) * leg(q, p) + g(p, a//2 + 1)) * g(q, (b+1)//2) * HS[q]
                ok += S_direct(n) == pred
print("7.2: %d values n = p^a q^b <= %d (p < q both 3 mod 4); holds: %d" % (cnt, NMAX, ok))
# 7.3 and 7.4: odd squarefree n
def sqfree(n): return all(e == 1 for e in factor(n).values())
def mu(n):
    f = factor(n); return 0 if any(e > 1 for e in f.values()) else (-1)**len(f)
cnt = ok3 = ok4 = 0; F = {}
for n in range(1, NMAX+1, 2):
    if not sqfree(n): continue
    cnt += 1; F[n] = f_direct(n)
    Ssum = sum((HS[d] for d in divisors(n) if d % 4 == 3), Fr(0))
    pred = -Ssum/2 if n % 4 == 1 else Fr(1-n, 4) - Ssum/2
    ok3 += F[n] == pred
    delta = lambda d: 1 if d % 4 == 3 else 0
    lhs = HS[n]*delta(n) if n % 4 == 3 else Fr(0)
    rhs = sum((mu(n//d) * (Fr(1-d, 2)*delta(d) - 2*F[d]) for d in divisors(n)), Fr(0))
    ok4 += lhs == rhs
print("7.3: %d odd squarefree n <= %d; holds: %d.   7.4: holds: %d" % (cnt, NMAX, ok3, ok4))
# 7.5: limits
for r in range(4):
    xs = [n for n in range(NMAX-2000, NMAX+1) if n % 4 == r]
    v = [float(f_direct(n))/n for n in xs]
    print("7.5: n = %d mod 4, n in [%d, %d]: f(n)/n in [%.4f, %.4f], mean %.5f" % (r, xs[0], xs[-1], min(v), max(v), sum(v)/len(v)))
# Chamberland-Dilcher propositions as consistency checks (f(2p), f(4p), prime powers) are implied by cd1; spot check:
print("f(2*13), f(2*11), f(4*11), f(4*13), f(4*7):", f_direct(26), f_direct(22), f_direct(44), f_direct(52), f_direct(28))
