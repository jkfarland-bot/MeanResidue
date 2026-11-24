module

public import Mathlib

@[expose] public section

/-!
# Mean quadratic residues and the Chamberland–Dilcher floor sums: statements

This file is the statement surface for the Palomar registry. It restates, with their exact library
definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development in
`MeanResidue/`.

## Definitions

* `S n = (1/n) ∑_{k<n} Rem(k² ÷ n)`, the mean quadratic residue of Chamberland and Dilcher
  (arXiv:2510.04387).
* `f n = ∑_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ - (n² - 1)/12`, their floor sum.
* `s n = #{k < n : n ∣ k²}`, the number of square roots of `0` modulo `n`.
* `defect n = (n - s n)/2 - S n`.
* `hB d = -(1/d) ∑_{a<d} a (a/d)` with the Jacobi symbol `(a/d)`: the Bernoulli form of the weighted
  class number `h*(-d)`. That `hB d = h*(-d)` for squarefree `d ≡ 3 (mod 4)` is Dirichlet's class
  number formula, which is quoted and not formalized.
* `cnt n a = #{x ∈ ℤ/n : x² = a}`.
* `δ d = 1` if `d ≡ 3 (mod 4)` and `0` otherwise.
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

/-- The number of square roots of `a` modulo `n`. -/
noncomputable def cnt (n : ℕ) (a : ℤ) : ℕ := Nat.card {x : ZMod n // x ^ 2 = (a : ZMod n)}

/-- `δ d = 1` if `d ≡ 3 (mod 4)` and `0` otherwise. -/
def δ (d : ℕ) : ℚ := if d % 4 = 3 then 1 else 0

/-- **Theorem 1.2, case `n ≡ 1 (mod 4)`**: `f n = (s n - 1)/4 - defect n / 2`. -/
theorem f_mod_four_eq_one (n : ℕ) (h : n % 4 = 1) : f n = ((s n : ℚ) - 1) / 4 - defect n / 2 := by
  sorry

/-- **Theorem 1.2, case `n ≡ 3 (mod 4)`**: `f n = (s n - n)/4 - defect n / 2`. -/
theorem f_mod_four_eq_three (n : ℕ) (h : n % 4 = 3) :
    f n = ((s n : ℚ) - n) / 4 - defect n / 2 := by
  sorry

/-- **Theorem 1.2, case `n ≡ 0 (mod 4)`**: `f n = n/8 + s n / 4 - defect n / 2`. -/
theorem f_mod_four_eq_zero (n : ℕ) (hn : 0 < n) (h : n % 4 = 0) :
    f n = (n : ℚ) / 8 + (s n : ℚ) / 4 - defect n / 2 := by
  sorry

/-- **Theorem 1.2, case `n ≡ 2 (mod 4)`**: `f n = -n/8 + (s n - 1)/4 - defect n / 2`. -/
theorem f_mod_four_eq_two (n : ℕ) (h : n % 4 = 2) :
    f n = -(n : ℚ) / 8 + ((s n : ℚ) - 1) / 4 - defect n / 2 := by
  sorry

/-- For odd squarefree `n`, the number of square roots of `a` modulo `n` is `∑_{d ∣ n} (a/d)`. -/
theorem cnt_eq_sum_jacobi {n : ℕ} (hn : Squarefree n) (hodd : Odd n) (a : ℤ) :
    (cnt n a : ℤ) = ∑ d ∈ n.divisors, jacobiSym a d := by
  sorry

/-- For squarefree `n`, `0` is the only square root of `0` modulo `n`. -/
theorem s_squarefree {n : ℕ} (hn : Squarefree n) : s n = 1 := by
  sorry

/-- **Theorem 1.1 at odd squarefree `n`, Bernoulli form**:
`(n - 1)/2 - S n = ∑_{d ∣ n, d ≡ 3 (mod 4)} hB d`. -/
theorem defect_squarefree {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    defect n = ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  sorry

/-- `S n = (n - 1)/2 - ∑_{d ∣ n, d ≡ 3 (4)} hB d` for odd squarefree `n` (Theorem 1.1). -/
theorem S_squarefree {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    S n = ((n : ℚ) - 1) / 2 - ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  sorry

/-- **Conjecture 7.3 (a)**, Bernoulli form: odd squarefree `n ≡ 1 (mod 4)`. -/
theorem conj_7_3_one {n : ℕ} (hn : Squarefree n) (h4 : n % 4 = 1) :
    f n = -(1 / 2) * ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  sorry

/-- **Conjecture 7.3 (b)**, Bernoulli form: odd squarefree `n ≡ 3 (mod 4)`. -/
theorem conj_7_3_three {n : ℕ} (hn : Squarefree n) (h4 : n % 4 = 3) :
    f n = (1 - (n : ℚ)) / 4 - (1 / 2) * ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  sorry

/-- **Conjecture 7.4**, Bernoulli form: for odd squarefree `n`,
`hB(n) δ(n) = ∑_{d ∣ n} μ(n/d) ((1 - d)/2 δ(d) - 2 f(d))`. -/
theorem conj_7_4 {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    hB n * δ n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius (n / d) : ℚ) * ((1 - (d : ℚ)) / 2 * δ d - 2 * f d) := by
  sorry

/-- **Bunyakovsky's identity**: `f p = 0` for primes `p ≡ 1 (mod 4)`. -/
theorem bunyakovsky {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) : f p = 0 := by
  sorry

/-- **Chamberland–Dilcher, Proposition 1.2**, Bernoulli form: `f p = (1 - p)/4 - hB(p)/2` for primes
`p ≡ 3 (mod 4)`. -/
theorem f_prime_three {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) :
    f p = (1 - (p : ℚ)) / 4 - hB p / 2 := by
  sorry

/-- **Chamberland–Dilcher (7.3)**, Bernoulli form: `S_{pq} = (pq - 1)/2 - hB p - hB q`. -/
theorem S_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) :
    S (p * q) = ((p * q : ℕ) - 1 : ℚ) / 2 - hB p - hB q := by
  sorry

/-- **Chamberland–Dilcher (7.4)**, Bernoulli form: `f(pq) = -(hB p + hB q)/2`. -/
theorem f_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) :
    f (p * q) = -(hB p + hB q) / 2 := by
  sorry

/-- **Square roots of a unit modulo `p^m`**: for an odd prime `p`, `m ≥ 1` and `p ∤ u`, the number of
square roots of `u` modulo `p^m` is `1 + (u/p)`. -/
theorem cnt_unit {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) (u : ℕ)
    (hu : ¬ p ∣ u) : (cnt (p ^ m) u : ℤ) = 1 + legendreSym p u := by
  sorry

end MeanResidue
