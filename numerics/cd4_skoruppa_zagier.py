# Check: Skoruppa-Zagier (Invent. Math. 94 (1988)), Prop. A.2, case a = 1, equals Theorem 1.1:
#  (i/f) sum_{nu mod f} cot(pi nu/f) sum_{lam mod f} e(nu lam^2/f) = -2 sum_{Delta<0, Delta | f, f/Delta squarefree} H(|Delta|)
#  and sum_{Delta | f, f/Delta squarefree} H(|Delta|) = sum_{c | f, c = 0,3 mod 4} h*(-c) = T(f),  2 Lambda(f) = LHS.
import cmath, math, os
os.environ['CD_NMAX'] = '400'
from cd_lib import *
from fractions import Fraction as Fr
def H(N):     # Hurwitz class number: sum over g^2 | N with -N/g^2 a discriminant of h*(-N/g^2)
    t = Fr(0); g = 1
    while g * g <= N:
        if N % (g * g) == 0 and (N // (g * g)) % 4 in (0, 3): t += HS[N // (g * g)]
        g += 1
    return t
def sqfree(m): return all(e == 1 for e in factor(m).values()) if m > 1 else True
bad1 = bad2 = 0; worst = 0
for f in range(1, 401):
    SZ = sum((H(D) for D in divisors(f) if sqfree(f // D)), Fr(0))
    T = T_of(f)
    bad1 += SZ != T
    lhs = 0
    for nu in range(1, f):
        G = sum(cmath.exp(2j * math.pi * nu * l * l / f) for l in range(f))
        lhs += 1 / math.tan(math.pi * nu / f) * G
    lhs = (1j / f) * lhs
    worst = max(worst, abs(lhs - (-2 * float(SZ))))
    Lam = -(Fr(f - s_of(f), 2) - S_direct(f)) if f > 1 else Fr(0)   # Lambda(f) = sum ((k^2/f)) = -defect(f)
    bad2 += abs(lhs.real - 2 * float(Lam)) > 1e-8
print("f <= 400: SZ Hurwitz sum = T(f) failures:", bad1, "; |LHS - (-2 SZ)| max = %.2e" % worst,
      "; LHS = 2 Lambda(f) failures:", bad2)
