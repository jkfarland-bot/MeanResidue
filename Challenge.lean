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
* `phi d b = ∑_{e ∣ d} μ(d/e) cnt(e, b)` (so that `cnt n b = ∑_{d ∣ n} phi d b`), through the
  arithmetic functions `cntAF b = cnt(·, b)` and `phiAF b = μ * cntAF b`.
* `Lam d g = -(1/d) ∑_{0<b<d} g(b) (b - d/2)`, a finite sawtooth sum, and `G d = Lam d (phi d ·)`, the
  contribution of the divisor `d` to `defect n`. Theorem 1.1 of the note is `G c = h*(-c)` for
  `c ≡ 0, 3 (mod 4)` and `G c = 0` otherwise; here it is stated through its ingredients: the divisor sum
  (`defect_eq_sum_G`), the vanishing (`G_one_mod_four`, `G_two_mod_four`), the values at fundamental
  discriminants (`G_fundamental`) and the conductor recursion (`G_conductor`). Dirichlet's class number
  formula (`hK c = h*(-c)` for fundamental `-c`) and the conductor formula
  `h*(ℓ² D) = (ℓ - (D/ℓ)) h*(D)` are quoted, not formalized.
* `kron c a = (-c/a)`, the Kronecker symbol of the discriminant `-c` (`c ≡ 0, 3 (mod 4)`), computed with
  Jacobi symbols; `hK c = -(1/c) ∑_{a<c} a (-c/a)`; `IsFundamental c`: `-c` is a fundamental
  discriminant.
* `geom ℓ e = 1 + ℓ + ⋯ + ℓ^(e-1)`, the `[e]_ℓ` of Chamberland and Dilcher.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

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

/-- `cnt` as a multiplicative arithmetic function. -/
noncomputable def cntAF (a : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (cnt n a : ℤ), by simp⟩

/-- `phi · b = μ * cnt(·, b)`. -/
noncomputable def phiAF (b : ℤ) : ArithmeticFunction ℤ := (μ : ArithmeticFunction ℤ) * cntAF b

/-- `phi d b = ∑_{e ∣ d} μ(d/e) cnt(e, b)`. -/
noncomputable def phi (d : ℕ) (b : ℤ) : ℤ := phiAF b d

/-- The sawtooth functional `Lam d g = -(1/d) ∑_{0<b<d} g(b) (b - d/2)`. -/
def Lam (d : ℕ) (g : ℤ → ℚ) : ℚ := -(∑ b ∈ Ico 1 d, g b * ((b : ℚ) - d / 2)) / d

/-- The contribution of the divisor `d`: `G d = Lam d (phi d ·)`. -/
noncomputable def G (d : ℕ) : ℚ := Lam d (fun b => (phi d b : ℚ))

/-- `[e]_ℓ = 1 + ℓ + ⋯ + ℓ^(e-1)`. -/
def geom (ℓ e : ℕ) : ℚ := ∑ i ∈ range e, (ℓ : ℚ) ^ i

/-- The Kronecker symbol `(-c/a)`, for `c ≡ 0, 3 (mod 4)` and `a ≥ 1`. -/
def kron (c a : ℕ) : ℤ := if c % 2 = 1 then jacobiSym a c else ZMod.χ₄ a * jacobiSym c a

/-- Bernoulli form of `h*(-c)` for a fundamental discriminant `-c`. -/
def hK (c : ℕ) : ℚ := -(∑ a ∈ range c, (a : ℚ) * kron c a) / c

/-- `-c` is a fundamental discriminant. -/
def IsFundamental (c : ℕ) : Prop :=
  ∃ m, Squarefree m ∧ ((c = m ∧ m % 4 = 3) ∨ (c = 4 * m ∧ (m % 4 = 1 ∨ m % 4 = 2)))

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

/-- **The recursion** `cnt (p^(i+2)) (p² b) = p · cnt (p^i) b`. -/
theorem cnt_pow_add_two_mul_sq (p : ℕ) [hp : Fact p.Prime] (i : ℕ) (b : ℤ) :
    cnt (p ^ (i + 2)) (p ^ 2 * b) = p * cnt (p ^ i) b := by
  sorry

/-- **Odd squares modulo `2^m`** (`m ≥ 3`): an odd `u` has `4` square roots if `u ≡ 1 (mod 8)` and none
otherwise. -/
theorem cnt_two_pow_unit (m : ℕ) {u : ℤ} (hu : u % 2 = 1) :
    cnt (2 ^ (m + 3)) u = if u % 8 = 1 then 4 else 0 := by
  sorry

/-- **Theorem 1.1, divisor form, for every `n ≥ 1`**: `(n - s(n))/2 - S n = ∑_{d ∣ n} G d`. -/
theorem defect_eq_sum_G {n : ℕ} (hn : 0 < n) : defect n = ∑ d ∈ n.divisors, G d := by
  sorry

/-- **Möbius-inverted form** (Corollary 1.3(d)): `∑_{d ∣ n} μ(n/d) defect(d) = G n`. -/
theorem moebius_defect {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℚ) * defect d = G n := by
  sorry

/-- `G d = 0` for `d ≡ 1 (mod 4)`. -/
theorem G_one_mod_four {d : ℕ} (h : d % 4 = 1) : G d = 0 := by
  sorry

/-- `G d = 0` for `d ≡ 2 (mod 4)`. -/
theorem G_two_mod_four {d : ℕ} (h : d % 4 = 2) : G d = 0 := by
  sorry

/-- **Odd `n`**: `defect n = ∑_{d ∣ n, d ≡ 3 (mod 4)} G d`. -/
theorem defect_odd {n : ℕ} (hn : Odd n) :
    defect n = ∑ d ∈ n.divisors with d % 4 = 3, G d := by
  sorry

/-- **Base case**: `G c = hB c` for squarefree `c ≡ 3 (mod 4)`. -/
theorem G_squarefree {c : ℕ} (hc : Squarefree c) (h4 : c % 4 = 3) : G c = hB c := by
  sorry

/-- **The conductor recursion** at odd `c ≡ 3 (mod 4)`: `G (ℓ² c) = (ℓ - (ℓ/c)) G c` for every
prime `ℓ`. -/
theorem G_peel {ℓ c : ℕ} (hℓ : ℓ.Prime) (hc : c % 4 = 3) :
    G (ℓ ^ 2 * c) = (ℓ - jacobiSym ℓ c) * G c := by
  sorry

/-- **Fundamental discriminants**: `G c = hK c` whenever `-c` is a fundamental discriminant
(Dirichlet's class number formula identifies `hK c` with `h*(-c)`; quoted). -/
theorem G_fundamental {c : ℕ} (hc : IsFundamental c) : G c = hK c := by
  sorry

/-- **The conductor recursion**: `G (ℓ² c) = (ℓ - (-c/ℓ)) G c` for every prime `ℓ` and every
`c > 0` with `c ≡ 0, 3 (mod 4)`. -/
theorem G_conductor {ℓ c : ℕ} (hℓ : ℓ.Prime) (hc0 : 0 < c) (hc : c % 4 = 0 ∨ c % 4 = 3) :
    G (ℓ ^ 2 * c) = (ℓ - kron c ℓ) * G c := by
  sorry

/-- **Conjecture 7.1 of Chamberland and Dilcher** (with the sign of the `h*(-pq)` term corrected),
Bernoulli form. -/
theorem conj_7_1 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 3)
    (α β : ℕ) :
    S (p ^ α * q ^ β) = (((p ^ α * q ^ β : ℕ) : ℚ) - (p ^ (α / 2) * q ^ (β / 2) : ℕ)) / 2 -
      geom q ((β + 1) / 2) * ((geom p (α / 2 + 1) - jacobiSym p q * geom p (α / 2)) * hB q +
        geom p ((α + 1) / 2) * hB (p * q)) := by
  sorry

/-- **Conjecture 7.2 of Chamberland and Dilcher**, Bernoulli form. -/
theorem conj_7_2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp4 : p % 4 = 3)
    (hq4 : q % 4 = 3) (α β : ℕ) :
    S (p ^ α * q ^ β) = (((p ^ α * q ^ β : ℕ) : ℚ) - (p ^ (α / 2) * q ^ (β / 2) : ℕ)) / 2 -
      (jacobiSym p q * geom q (β / 2) + geom q (β / 2 + 1)) * geom p ((α + 1) / 2) * hB p -
      (jacobiSym q p * geom p (α / 2) + geom p (α / 2 + 1)) * geom q ((β + 1) / 2) * hB q := by
  sorry

/-- **Conjecture 7.5 from a class number bound**: if `|G c| ≤ C √c (1 + log c)`, then
`f(n)/n → 1/8, 0, -1/8, -1/4` along `n ≡ 0, 1, 2, 3 (mod 4)`. (The bound holds with `C = 1`; Weyl.lean
proves the conjecture without it.) -/
theorem conj_7_5_of_class_number_bound {C : ℝ}
    (hC : ∀ c : ℕ, 0 < c → |(G c : ℝ)| ≤ C * Real.sqrt c * (1 + Real.log c)) :
    Tendsto (fun k : ℕ => (f (4 * k) : ℝ) / (4 * k : ℕ)) atTop (𝓝 (1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 1) : ℝ) / (4 * k + 1 : ℕ)) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 2) : ℝ) / (4 * k + 2 : ℕ)) atTop (𝓝 (-1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 3) : ℝ) / (4 * k + 3 : ℕ)) atTop (𝓝 (-1 / 4)) := by
  sorry

/-- **The unconditional bound**: `defect(n)² ≤ n √n (1 + log n)³`. -/
theorem defect_sq_le (n : ℕ) (hn : 0 < n) :
    ((defect n : ℚ) : ℝ) ^ 2 ≤ n * Real.sqrt n * (1 + Real.log n) ^ 3 := by
  sorry

/-- **Conjecture 7.5 of Chamberland and Dilcher** (with the fourth limit read as `f(4n+3)/(4n+3)`):
`f(n)/n → 1/8, 0, -1/8, -1/4` as `n → ∞` through `n ≡ 0, 1, 2, 3 (mod 4)`. -/
theorem conj_7_5 :
    Tendsto (fun k : ℕ => (f (4 * k) : ℝ) / (4 * k : ℕ)) atTop (𝓝 (1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 1) : ℝ) / (4 * k + 1 : ℕ)) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 2) : ℝ) / (4 * k + 2 : ℕ)) atTop (𝓝 (-1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 3) : ℝ) / (4 * k + 3 : ℕ)) atTop (𝓝 (-1 / 4)) := by
  sorry

end MeanResidue
