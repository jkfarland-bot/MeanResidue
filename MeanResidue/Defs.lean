module

public import Mathlib

@[expose] public section

/-!
# Definitions

* `S n = (1/n) ∑_{k<n} Rem(k² ÷ n)`, the mean quadratic residue of Chamberland and Dilcher.
* `f n = ∑_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ - (n² - 1)/12`, their floor sum (Bunyakovsky's sum minus its value
  at primes `p ≡ 1 (mod 4)`).
* `s n = #{k < n : n ∣ k²}`, the number of square roots of `0` modulo `n`; it is the largest
  integer whose square divides `n`.
* `defect n = (n - s n)/2 - S n`. The main theorem of the paper says that `defect n` is the sum of
  the weighted class numbers `h*(-c)` over the divisors `c ≡ 0, 3 (mod 4)` of `n`.
* `hB d = -(1/d) ∑_{a<d} a (a/d)`, with the Jacobi symbol `(a/d)`. For squarefree `d ≡ 3 (mod 4)`
  this is the weighted class number `h*(-d)` by Dirichlet's class number formula (quoted, not
  formalized): `hB 3 = 1/3`, `hB 7 = 1`, `hB 23 = 3`.
-/

open Finset

namespace MeanResidue

/-- The mean quadratic residue `S n = (1/n) ∑_{k<n} Rem(k² ÷ n)`. -/
def S (n : ℕ) : ℚ := (∑ k ∈ range n, ((k ^ 2 % n : ℕ) : ℚ)) / n

/-- The floor sum `f n = ∑_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ - (n² - 1)/12`. -/
def f (n : ℕ) : ℚ := (∑ j ∈ Icc 1 (n / 4), (Nat.sqrt (j * n) : ℚ)) - ((n : ℚ) ^ 2 - 1) / 12

/-- `s n = #{k < n : n ∣ k²}`. -/
def s (n : ℕ) : ℕ := #{k ∈ range n | n ∣ k ^ 2}

/-- The defect `(n - s n)/2 - S n`. -/
def defect (n : ℕ) : ℚ := ((n : ℚ) - s n) / 2 - S n

/-- The Bernoulli form of the weighted class number of `-d`: `hB d = -(1/d) ∑_{a<d} a (a/d)`. -/
def hB (d : ℕ) : ℚ := -(∑ a ∈ range d, (a : ℚ) * jacobiSym a d) / d

end MeanResidue
