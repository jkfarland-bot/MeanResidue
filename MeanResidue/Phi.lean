module

public import MeanResidue.RootCount

@[expose] public section

/-!
# The divisor decomposition of the root count

`phi d b = ∑_{e ∣ d} μ(d/e) cnt(e, b)`, so that `cnt n b = ∑_{d ∣ n} phi d b` (Möbius inversion).
For fixed `b`, `d ↦ phi d b` is multiplicative, and its values at prime powers follow from the root
counts of RootCount.lean. For odd `d` and `x` prime to `d`, `phi d (x b) = (x/d) phi d b`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace MeanResidue

/-- `phi · b = μ * cnt(·, b)`. -/
noncomputable def phiAF (b : ℤ) : ArithmeticFunction ℤ := (μ : ArithmeticFunction ℤ) * cntAF b

/-- `phi d b = ∑_{e ∣ d} μ(d/e) cnt(e, b)`. -/
noncomputable def phi (d : ℕ) (b : ℤ) : ℤ := phiAF b d

theorem isMultiplicative_phiAF (b : ℤ) : (phiAF b).IsMultiplicative :=
  isMultiplicative_moebius.mul (isMultiplicative_cntAF b)

theorem phi_one (b : ℤ) : phi 1 b = 1 := (isMultiplicative_phiAF b).map_one

theorem phi_mul {m n : ℕ} (h : m.Coprime n) (b : ℤ) : phi (m * n) b = phi m b * phi n b :=
  (isMultiplicative_phiAF b).map_mul_of_coprime h

theorem phiAF_mul_zeta (b : ℤ) : phiAF b * (ζ : ArithmeticFunction ℤ) = cntAF b := by
  rw [phiAF, mul_comm (μ : ArithmeticFunction ℤ), mul_assoc, moebius_mul_coe_zeta, mul_one]

/-- **Möbius inversion**: `cnt n b = ∑_{d ∣ n} phi d b`. -/
theorem cnt_eq_sum_phi {n : ℕ} (hn : n ≠ 0) (b : ℤ) :
    (cnt n b : ℤ) = ∑ d ∈ n.divisors, phi d b := by
  rw [← cntAF_apply b hn, ← phiAF_mul_zeta, coe_mul_zeta_apply]
  rfl

/-- `phi d b` depends only on `b` modulo `d`. -/
theorem phi_congr {d : ℕ} {b b' : ℤ} (h : (d : ℤ) ∣ b - b') : phi d b = phi d b' := by
  unfold phi phiAF
  rw [mul_apply, mul_apply]
  apply sum_congr rfl
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have hx2 : (x.2 : ℤ) ∣ (d : ℤ) := by
    rw [← hx.1]; push_cast; exact dvd_mul_left _ _
  simp only [cntAF, coe_mk]
  rw [cnt_congr (hx2.trans h)]

theorem phi_add_mul (d : ℕ) (b k : ℤ) : phi d (b + d * k) = phi d b :=
  phi_congr ⟨k, by ring⟩

/-- Multiplying by the square of a unit does not change `phi`. -/
theorem phi_sq_mul {d : ℕ} {x : ℤ} (hx : IsCoprime x d) (b : ℤ) : phi d (x ^ 2 * b) = phi d b := by
  unfold phi phiAF
  rw [mul_apply, mul_apply]
  apply sum_congr rfl
  intro y hy
  rw [Nat.mem_divisorsAntidiagonal] at hy
  have hy2 : (y.2 : ℤ) ∣ (d : ℤ) := by
    rw [← hy.1]; push_cast; exact dvd_mul_left _ _
  simp only [cntAF, coe_mk]
  rw [cnt_sq_mul (hx.of_isCoprime_of_dvd_right hy2)]

theorem phi_prime_pow_succ (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (b : ℤ) :
    phi (p ^ (k + 1)) b = cnt (p ^ (k + 1)) b - cnt (p ^ k) b := by
  have h1 := cnt_eq_sum_phi (pow_ne_zero (k + 1) hp.out.ne_zero) b
  have h2 := cnt_eq_sum_phi (pow_ne_zero k hp.out.ne_zero) b
  rw [Nat.sum_divisors_prime_pow hp.out] at h1 h2
  rw [sum_range_succ] at h1
  rw [h1, h2]
  ring

/-! ### Values at prime powers -/

section PrimePow

variable (p : ℕ) [hp : Fact p.Prime]

theorem phi_prime (hp2 : p ≠ 2) (b : ℤ) : phi p b = jacobiSym b p := by
  have h := phi_prime_pow_succ p 0 b
  rw [zero_add, pow_one, pow_zero, cnt_one, cnt_prime p hp2] at h
  rw [h]
  push_cast
  ring

theorem phi_pow_unit (hp2 : p ≠ 2) (k : ℕ) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    phi (p ^ (k + 2)) b = 0 := by
  rw [phi_prime_pow_succ, cnt_unit_int p hp2 (by omega) hb, cnt_unit_int p hp2 (by omega) hb]
  ring

theorem phi_sq_of_exact {b : ℤ} (h1 : (p : ℤ) ∣ b) (h2 : ¬ (p : ℤ) ^ 2 ∣ b) :
    phi (p ^ 2) b = -1 := by
  rw [phi_prime_pow_succ p 1, cnt_pow_eq_zero p le_rfl h1 h2, pow_one, cnt_prime_of_dvd p h1]
  norm_num

theorem phi_pow_of_exact (k : ℕ) {b : ℤ} (h1 : (p : ℤ) ∣ b) (h2 : ¬ (p : ℤ) ^ 2 ∣ b) :
    phi (p ^ (k + 3)) b = 0 := by
  rw [phi_prime_pow_succ p (k + 2), cnt_pow_eq_zero p (by omega) h1 h2,
    cnt_pow_eq_zero p (by omega) h1 h2]
  simp

theorem phi_sq_sq (b : ℤ) : phi (p ^ 2) ((p : ℤ) ^ 2 * b) = p - 1 := by
  rw [phi_prime_pow_succ p 1, show (1 : ℕ) + 1 = 0 + 2 from rfl, cnt_pow_add_two_mul_sq, pow_zero,
    cnt_one, pow_one, cnt_prime_of_dvd p (dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) b)]
  push_cast
  ring

theorem phi_pow_sq (k : ℕ) (b : ℤ) :
    phi (p ^ (k + 3)) ((p : ℤ) ^ 2 * b) = p * phi (p ^ (k + 1)) b := by
  rw [phi_prime_pow_succ p (k + 2), phi_prime_pow_succ p k, show k + 2 + 1 = (k + 1) + 2 from rfl,
    cnt_pow_add_two_mul_sq, cnt_pow_add_two_mul_sq]
  push_cast
  ring

/-- For odd `p`: `phi (p²) b = p [p² ∣ b] - [p ∣ b]`. -/
theorem phi_sq_odd (hp2 : p ≠ 2) (b : ℤ) :
    phi (p ^ 2) b = (if (p : ℤ) ^ 2 ∣ b then (p : ℤ) else 0) - (if (p : ℤ) ∣ b then 1 else 0) := by
  by_cases h1 : (p : ℤ) ∣ b
  · by_cases h2 : (p : ℤ) ^ 2 ∣ b
    · obtain ⟨c, rfl⟩ := h2
      rw [phi_sq_sq, ite_eq_left (dvd_mul_right _ _), ite_eq_left h1]
    · rw [phi_sq_of_exact p h1 h2, ite_eq_right h2, ite_eq_left h1]
      ring
  · have h2 : ¬ (p : ℤ) ^ 2 ∣ b := fun h => h1 ((dvd_pow_self _ two_ne_zero).trans h)
    rw [show p ^ 2 = p ^ (0 + 2) from rfl, phi_pow_unit p hp2 0 h1, ite_eq_right h2, ite_eq_right h1]
    ring

/-- For odd `p` and `k ≥ 1`: `phi (p^(k+2)) b = p [p² ∣ b] phi (p^k) (b/p²)`. -/
theorem phi_pow_add_two_odd (hp2 : p ≠ 2) (k : ℕ) (b : ℤ) :
    phi (p ^ (k + 3)) b =
      if (p : ℤ) ^ 2 ∣ b then (p : ℤ) * phi (p ^ (k + 1)) (b / (p : ℤ) ^ 2) else 0 := by
  have hpZ0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.out.ne_zero)
  by_cases h2 : (p : ℤ) ^ 2 ∣ b
  · obtain ⟨c, rfl⟩ := h2
    rw [phi_pow_sq, ite_eq_left (dvd_mul_right _ _), Int.mul_ediv_cancel_left _ hpZ0]
  · rw [ite_eq_right h2]
    by_cases h1 : (p : ℤ) ∣ b
    · exact phi_pow_of_exact p k h1 h2
    · rw [show k + 3 = (k + 1) + 2 from rfl]
      exact phi_pow_unit p hp2 (k + 1) h1

/-- The twist rule at an odd prime power. -/
theorem phi_prime_pow_twist (hp2 : p ≠ 2) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) (k : ℕ) (b : ℤ) :
    phi (p ^ k) (x * b) = jacobiSym x p ^ k * phi (p ^ k) b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hJ : jacobiSym x p ^ 2 = 1 := by
    apply jacobiSym.sq_one
    exact Int.isCoprime_iff_gcd_eq_one.1 ((hpZ.coprime_iff_not_dvd).2 hx).symm
  induction k using Nat.strong_induction_on generalizing b with
  | _ k ih =>
  match k with
  | 0 => simp [phi_one]
  | 1 =>
    rw [pow_one, phi_prime p hp2, phi_prime p hp2, jacobiSym.mul_left]
    ring
  | k + 2 =>
    by_cases h1 : (p : ℤ) ∣ b
    · by_cases h2 : (p : ℤ) ^ 2 ∣ b
      · obtain ⟨c, rfl⟩ := h2
        rw [show x * ((p : ℤ) ^ 2 * c) = (p : ℤ) ^ 2 * (x * c) by ring]
        match k with
        | 0 =>
          rw [phi_sq_sq, phi_sq_sq, hJ]
          ring
        | k' + 1 =>
          rw [show k' + 1 + 2 = k' + 3 from rfl, phi_pow_sq, phi_pow_sq, ih (k' + 1) (by omega)]
          rw [show jacobiSym x p ^ (k' + 3) = jacobiSym x p ^ (k' + 1) * jacobiSym x p ^ 2 by ring,
            hJ]
          ring
      · have h1' : (p : ℤ) ∣ x * b := dvd_mul_of_dvd_right h1 x
        have h2' : ¬ (p : ℤ) ^ 2 ∣ x * b := by
          intro h
          apply h2
          exact (((hpZ.coprime_iff_not_dvd).2 hx).pow_left).dvd_of_dvd_mul_left h
        match k with
        | 0 =>
          rw [phi_sq_of_exact p h1' h2', phi_sq_of_exact p h1 h2, hJ]
          ring
        | k' + 1 =>
          rw [show k' + 1 + 2 = k' + 3 from rfl, phi_pow_of_exact p k' h1' h2',
            phi_pow_of_exact p k' h1 h2]
          ring
    · have h1' : ¬ (p : ℤ) ∣ x * b := fun h => (hpZ.dvd_or_dvd h).elim hx h1
      rw [phi_pow_unit p hp2 k h1', phi_pow_unit p hp2 k h1]
      ring

end PrimePow

/-! ### `p = 2` -/

theorem phi_two (b : ℤ) : phi 2 b = 0 := by
  have h := phi_prime_pow_succ 2 0 b
  rw [zero_add, pow_one, pow_zero, cnt_one, cnt_two] at h
  simpa using h

theorem phi_four_unit {u : ℤ} (hu : u % 2 = 1) : phi 4 u = ZMod.χ₄ u := by
  have h := phi_prime_pow_succ 2 1 u
  rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num, pow_one, cnt_four_unit hu, cnt_two] at h
  rw [h]
  push_cast
  ring

theorem phi_four (b : ℤ) :
    phi 4 b = (if (4 : ℤ) ∣ b then 2 else 0) - (if (2 : ℤ) ∣ b then 1 else 0) + ZMod.χ₄ b := by
  by_cases h1 : (2 : ℤ) ∣ b
  · have hχ : ZMod.χ₄ b = 0 := by
      rw [ZMod.χ₄_int_eq_if_mod_four, ite_eq_left (by omega)]
    rw [hχ, ite_eq_left h1]
    by_cases h2 : (4 : ℤ) ∣ b
    · obtain ⟨c, rfl⟩ := h2
      have := phi_sq_sq 2 c
      norm_num at this
      rw [this, ite_eq_left (dvd_mul_right _ _)]
      norm_num
    · have h2' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ b := by norm_num; exact h2
      have := phi_sq_of_exact 2 (by exact_mod_cast h1) h2'
      norm_num at this
      rw [this, ite_eq_right h2]
      norm_num
  · have hu : b % 2 = 1 := by omega
    rw [phi_four_unit hu, ite_eq_right h1, ite_eq_right (fun h => h1 ((by norm_num : (2 : ℤ) ∣ 4).trans h))]
    ring

theorem phi_eight_unit {u : ℤ} (hu : u % 2 = 1) : phi 8 u = ZMod.χ₈ u + ZMod.χ₈' u := by
  have h := phi_prime_pow_succ 2 2 u
  have hc8 : cnt 8 u = if u % 8 = 1 then 4 else 0 := by simpa using cnt_two_pow_unit 0 hu
  rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num, hc8,
    show (2 : ℕ) ^ 2 = 4 by norm_num, cnt_four_unit hu] at h
  rw [h, ZMod.χ₄_int_eq_if_mod_four, ZMod.χ₈_int_eq_if_mod_eight, ZMod.χ₈'_int_eq_if_mod_eight]
  have h8 : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8 <;> simp [h8, show u % 2 = 1 from hu] <;> omega

theorem phi_eight_even {b : ℤ} (hb : (2 : ℤ) ∣ b) : phi 8 b = 0 := by
  by_cases h2 : (4 : ℤ) ∣ b
  · obtain ⟨c, rfl⟩ := h2
    have := phi_pow_sq 2 0 c
    norm_num at this
    rw [this, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, phi_two]
    ring
  · have h2' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ b := by norm_num; exact h2
    have := phi_pow_of_exact 2 0 (by exact_mod_cast hb) h2'
    norm_num at this
    exact this

theorem phi_two_pow_unit (k : ℕ) {u : ℤ} (hu : u % 2 = 1) : phi (2 ^ (k + 4)) u = 0 := by
  rw [phi_prime_pow_succ 2 (k + 3), cnt_two_pow_unit (k + 1) hu, cnt_two_pow_unit k hu]
  simp

/-- `phi (2^(k+4)) b = 2 [4 ∣ b] phi (2^(k+2)) (b/4)`. -/
theorem phi_two_pow_add_four (k : ℕ) (b : ℤ) :
    phi (2 ^ (k + 4)) b = if (4 : ℤ) ∣ b then 2 * phi (2 ^ (k + 2)) (b / 4) else 0 := by
  by_cases h2 : (4 : ℤ) ∣ b
  · obtain ⟨c, rfl⟩ := h2
    have := phi_pow_sq 2 (k + 1) c
    norm_num at this
    rw [ite_eq_left (dvd_mul_right _ _), Int.mul_ediv_cancel_left _ (by norm_num),
      show k + 4 = k + 1 + 3 from rfl, this]
  · rw [ite_eq_right h2]
    by_cases h1 : (2 : ℤ) ∣ b
    · have h2' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ b := by norm_num; exact h2
      rw [show k + 4 = (k + 1) + 3 from rfl]
      exact phi_pow_of_exact 2 (k + 1) (by exact_mod_cast h1) h2'
    · exact phi_two_pow_unit k (by omega)

/-! ### Odd `d`: twist and parity -/

/-- **The twist rule**: for odd `d` and `x` prime to `d`, `phi d (x b) = (x/d) phi d b`. -/
theorem phi_twist {d : ℕ} (hd : Odd d) {x : ℤ} (hx : IsCoprime x d) (b : ℤ) :
    phi d (x * b) = jacobiSym x d * phi d b := by
  have hd0 : d ≠ 0 := by rintro rfl; exact absurd hd (by decide)
  have hmul : ((jacAF x).pmul (phiAF b)).IsMultiplicative :=
    (isMultiplicative_jacAF x).pmul (isMultiplicative_phiAF b)
  have h1 : phiAF (x * b) d = ((jacAF x).pmul (phiAF b)) d := by
    rw [IsMultiplicative.multiplicative_factorization _ (isMultiplicative_phiAF (x * b)) hd0,
      IsMultiplicative.multiplicative_factorization _ hmul hd0]
    apply Finsupp.prod_congr
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk hpp
    have hp2 : p ≠ 2 := by
      intro h2
      have := Odd.of_dvd_nat hd hpn
      rw [h2] at this
      exact absurd this (by decide)
    have hpx : ¬ (p : ℤ) ∣ x := by
      intro h
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
      exact hpZ.not_isUnit (hx.isUnit_of_dvd' h (by exact_mod_cast hpn))
    rw [pmul_apply, jacAF_apply x (pow_ne_zero _ hpp.ne_zero), jacobiSym.pow_right]
    exact phi_prime_pow_twist p hp2 hpx _ b
  have h2 : phi d (x * b) = phiAF (x * b) d := rfl
  rw [h2, h1, pmul_apply, jacAF_apply x hd0]
  rfl

/-- **Parity**: for odd `d`, `phi d (-b) = χ₄(d) phi d b`. -/
theorem phi_neg {d : ℕ} (hd : Odd d) (b : ℤ) : phi d (-b) = ZMod.χ₄ d * phi d b := by
  rw [← jacobiSym.at_neg_one hd, ← phi_twist hd isCoprime_one_left.neg_left b, neg_one_mul]

/-- For odd squarefree `c`, `phi c b = (b/c)`. -/
theorem phi_squarefree {c : ℕ} (hc : Squarefree c) (hodd : Odd c) (b : ℤ) :
    phi c b = jacobiSym b c := by
  have hc0 : c ≠ 0 := hc.ne_zero
  have h1 : phiAF b c = jacAF b c := by
    rw [IsMultiplicative.multiplicative_factorization _ (isMultiplicative_phiAF b) hc0,
      IsMultiplicative.multiplicative_factorization _ (isMultiplicative_jacAF b) hc0]
    apply Finsupp.prod_congr
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ c := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.factorization_eq_one_of_squarefree hc hpp hpn, pow_one]
    have := Fact.mk hpp
    have hp2 : p ≠ 2 := by
      intro h2
      have := Odd.of_dvd_nat hodd hpn
      rw [h2] at this
      exact absurd this (by decide)
    rw [jacAF_apply b hpp.ne_zero]
    exact phi_prime p hp2 b
  show phiAF b c = _
  rw [h1, jacAF_apply b hc0]

end MeanResidue
