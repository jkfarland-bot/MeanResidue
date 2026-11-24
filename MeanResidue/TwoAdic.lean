module

public import MeanResidue.TwoPrimes

@[expose] public section

/-!
# The `2`-adic factor

`Lam` sees only the odd part `od g (b) = (g b - g (-b))/2` of a periodic function. For `j = k + 2 ≥ 2`
the even and odd parts of `A_j = phi (2^j)` are eigenfunctions of every odd twist `b ↦ ℓ b`:
`ev A_j (ℓ b) = χ₈(ℓ)^k ev A_j b` and `od A_j (ℓ b) = χ₄(ℓ) χ₈(ℓ)^k od A_j b`.
(`A_4 = ν₂ + χ₄`, `A_8 = χ₈ + χ₈'`, `A_(j+2) = 2 · dil 4 A_j` for `j ≥ 4`.)
-/

open Finset

namespace MeanResidue

/-- The even part of a function. -/
def ev (g : ℤ → ℚ) (b : ℤ) : ℚ := (g b + g (-b)) / 2

/-- The odd part of a function. -/
def od (g : ℤ → ℚ) (b : ℤ) : ℚ := (g b - g (-b)) / 2

theorem ev_add_od (g : ℤ → ℚ) (b : ℤ) : ev g b + od g b = g b := by
  unfold ev od
  ring

theorem ev_neg (g : ℤ → ℚ) (b : ℤ) : ev g (-b) = ev g b := by
  unfold ev
  rw [neg_neg]
  ring

theorem od_neg (g : ℤ → ℚ) (b : ℤ) : od g (-b) = -od g b := by
  unfold od
  rw [neg_neg]
  ring

theorem periodic_neg {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (b : ℤ) :
    g (-(b + m)) = g (-b) := by
  have := hg (-(b + m))
  rw [show -(b + (m : ℤ)) + m = -b by ring] at this
  exact this.symm

theorem ev_periodic {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (b : ℤ) :
    ev g (b + m) = ev g b := by
  unfold ev
  rw [hg, periodic_neg hg]

theorem od_periodic {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (b : ℤ) :
    od g (b + m) = od g b := by
  unfold od
  rw [hg, periodic_neg hg]

/-- `Lam` sees only the odd part. -/
theorem Lam_od {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) : Lam m (od g) = Lam m g := by
  have h1 : Lam m g = Lam m (fun b => ev g b + od g b) := by
    congr 1
    funext b
    rw [ev_add_od]
  rw [h1, Lam_add, Lam_even (ev_periodic hg) (ev_neg g), zero_add]

/-- `Lam` of an odd periodic function. -/
theorem Lam_odd {m : ℕ} (hm : 0 < m) {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b)
    (ho : ∀ b, g (-b) = -g b) : Lam m g = -(∑ b ∈ range m, (b : ℚ) * g b) / m := by
  have h0 : g 0 = 0 := by
    have := ho 0
    rw [neg_zero] at this
    linarith
  have hsum : ∑ b ∈ range m, g b = 0 := by
    have h := sum_Ico_reflect (fun x => g x) 1 (show m ≤ m + 1 by omega)
    simp only [show m + 1 - m = 1 by omega, show m + 1 - 1 = m by omega] at h
    have h2 : ∑ b ∈ Ico 1 m, g ((m - b : ℕ) : ℤ) = -∑ b ∈ Ico 1 m, g b := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro b hb
      rw [mem_Ico] at hb
      rw [show ((m - b : ℕ) : ℤ) = -(b : ℤ) + m by push_cast [Nat.cast_sub hb.2.le]; ring, hg, ho]
    rw [h2] at h
    rw [range_split m hm (fun b => g b), Nat.cast_zero, h0, zero_add]
    linarith
  rw [Lam_eq_range hm, hsum, h0]
  ring

/-! ### Characters -/

theorem chi4_mul (a b : ℤ) : (ZMod.χ₄ ((a * b : ℤ) : ZMod 4) : ℚ) = ZMod.χ₄ a * ZMod.χ₄ b := by
  rw [Int.cast_mul, map_mul]
  push_cast
  ring

theorem chi8_mul (a b : ℤ) : (ZMod.χ₈ ((a * b : ℤ) : ZMod 8) : ℚ) = ZMod.χ₈ a * ZMod.χ₈ b := by
  rw [Int.cast_mul, map_mul]
  push_cast
  ring

theorem chi8'_mul (a b : ℤ) : (ZMod.χ₈' ((a * b : ℤ) : ZMod 8) : ℚ) = ZMod.χ₈' a * ZMod.χ₈' b := by
  rw [Int.cast_mul, map_mul]
  push_cast
  ring

theorem chi8_neg (b : ℤ) : ZMod.χ₈ ((-b : ℤ) : ZMod 8) = ZMod.χ₈ b := by
  push_cast
  have key : ∀ x : ZMod 8, ZMod.χ₈ (-x) = ZMod.χ₈ x := by decide
  exact key _

theorem chi8'_neg (b : ℤ) : ZMod.χ₈' ((-b : ℤ) : ZMod 8) = -ZMod.χ₈' b := by
  push_cast
  have key : ∀ x : ZMod 8, ZMod.χ₈' (-x) = -ZMod.χ₈' x := by decide
  exact key _

theorem chi4_sq {ℓ : ℤ} (hℓ : ℓ % 2 = 1) : (ZMod.χ₄ ℓ : ℚ) ^ 2 = 1 := by
  rw [ZMod.χ₄_int_eq_if_mod_four]
  split_ifs <;> norm_num
  omega

theorem chi8_sq {ℓ : ℤ} (hℓ : ℓ % 2 = 1) : (ZMod.χ₈ ℓ : ℚ) ^ 2 = 1 := by
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  split_ifs <;> norm_num
  omega

theorem chi8'_eq (b : ℤ) : (ZMod.χ₈' b : ℚ) = ZMod.χ₄ b * ZMod.χ₈ b := by
  rw [ZMod.χ₈'_int_eq_χ₄_mul_χ₈]
  push_cast
  ring

/-! ### `ν₂` and `dil 4` -/

theorem nu_neg (q : ℕ) (b : ℤ) : nu q (-b) = nu q b := by
  unfold nu
  simp only [dvd_neg]

theorem nu_two_mul {ℓ : ℤ} (hℓ : ℓ % 2 = 1) (b : ℤ) : nu 2 (ℓ * b) = nu 2 b := by
  have h2 : IsCoprime (2 : ℤ) ℓ := (Int.prime_two.coprime_iff_not_dvd).2 (by omega)
  have h4 : IsCoprime (4 : ℤ) ℓ := by
    have := h2.pow_left (m := 2)
    norm_num at this
    exact this
  unfold nu
  push_cast
  have e1 : (4 : ℤ) ∣ ℓ * b ↔ (4 : ℤ) ∣ b :=
    ⟨fun h => h4.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h ℓ⟩
  have e2 : (2 : ℤ) ∣ ℓ * b ↔ (2 : ℤ) ∣ b :=
    ⟨fun h => h2.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h ℓ⟩
  simp only [e1, e2]

theorem dil_four_neg (g : ℤ → ℚ) (b : ℤ) :
    dil 4 g (-b) = dil 4 (fun x => g (-x)) b := by
  unfold dil
  push_cast
  simp only [dvd_neg]
  split_ifs with h
  · rw [Int.neg_ediv_of_dvd h]
  · rfl

theorem dil_four_mul {ℓ : ℤ} (hℓ : ℓ % 2 = 1) (g : ℤ → ℚ) (b : ℤ) :
    dil 4 g (ℓ * b) = dil 4 (fun x => g (ℓ * x)) b := by
  have h4 : IsCoprime (4 : ℤ) ℓ := by
    have : IsCoprime ((2 : ℤ) ^ 2) ℓ := ((Int.prime_two.coprime_iff_not_dvd).2 (by omega)).pow_left
    norm_num at this
    exact this
  unfold dil
  push_cast
  have e : (4 : ℤ) ∣ ℓ * b ↔ (4 : ℤ) ∣ b :=
    ⟨fun h => h4.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h ℓ⟩
  simp only [e]
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    rw [show ℓ * (4 * t) = 4 * (ℓ * t) by ring, Int.mul_ediv_cancel_left _ (by norm_num),
      Int.mul_ediv_cancel_left _ (by norm_num)]
  · rfl

/-! ### `A_j = phi (2^j)` -/

/-- `A j = phi (2^j)` as a rational function of `b`. -/
noncomputable def A (j : ℕ) (b : ℤ) : ℚ := (phi (2 ^ j) b : ℚ)

theorem A_two (b : ℤ) : A 2 b = nu 2 b + ZMod.χ₄ b := by
  rw [A, show (2 : ℕ) ^ 2 = 4 by norm_num, phi_four_eq_nu]

theorem A_three (b : ℤ) : A 3 b = ZMod.χ₈ b + ZMod.χ₈' b := by
  rw [A, show (2 : ℕ) ^ 3 = 8 by norm_num]
  by_cases h : (2 : ℤ) ∣ b
  · rw [phi_eight_even h, ZMod.χ₈_int_eq_if_mod_eight, ZMod.χ₈'_int_eq_if_mod_eight,
      ite_eq_left (by omega), ite_eq_left (by omega)]
    simp
  · rw [phi_eight_unit (by omega)]
    push_cast
    ring

theorem A_add_four (k : ℕ) (b : ℤ) : A (k + 4) b = 2 * dil 4 (A (k + 2)) b := by
  rw [A, phi_two_pow_add_four, dil]
  push_cast
  split_ifs <;> simp [A]

theorem ev_A_two (b : ℤ) : ev (A 2) b = nu 2 b := by
  unfold ev
  rw [A_two, A_two, nu_neg, chi4_neg]
  push_cast
  ring

theorem od_A_two (b : ℤ) : od (A 2) b = ZMod.χ₄ b := by
  unfold od
  rw [A_two, A_two, nu_neg, chi4_neg]
  push_cast
  ring

theorem ev_A_three (b : ℤ) : ev (A 3) b = ZMod.χ₈ b := by
  unfold ev
  rw [A_three, A_three, chi8_neg, chi8'_neg]
  push_cast
  ring

theorem od_A_three (b : ℤ) : od (A 3) b = ZMod.χ₈' b := by
  unfold od
  rw [A_three, A_three, chi8_neg, chi8'_neg]
  push_cast
  ring

theorem ev_A_add_four (k : ℕ) (b : ℤ) : ev (A (k + 4)) b = 2 * dil 4 (ev (A (k + 2))) b := by
  unfold ev
  rw [A_add_four, A_add_four, dil_four_neg]
  unfold dil
  split_ifs <;> ring

theorem od_A_add_four (k : ℕ) (b : ℤ) : od (A (k + 4)) b = 2 * dil 4 (od (A (k + 2))) b := by
  unfold od
  rw [A_add_four, A_add_four, dil_four_neg]
  unfold dil
  split_ifs <;> ring

/-- **The `2`-adic twist**: for odd `ℓ`, `ev A_(k+2) (ℓ b) = χ₈(ℓ)^k ev A_(k+2) b` and
`od A_(k+2) (ℓ b) = χ₄(ℓ) χ₈(ℓ)^k od A_(k+2) b`. -/
theorem A_twist {ℓ : ℤ} (hℓ : ℓ % 2 = 1) (k : ℕ) :
    (∀ b, ev (A (k + 2)) (ℓ * b) = (ZMod.χ₈ ℓ : ℚ) ^ k * ev (A (k + 2)) b) ∧
    (∀ b, od (A (k + 2)) (ℓ * b) = (ZMod.χ₄ ℓ : ℚ) * (ZMod.χ₈ ℓ : ℚ) ^ k * od (A (k + 2)) b) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  match k with
  | 0 =>
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rw [ev_A_two, ev_A_two, nu_two_mul hℓ]
      ring
    · rw [od_A_two, od_A_two, chi4_mul]
      ring
  | 1 =>
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rw [ev_A_three, ev_A_three, chi8_mul]
      ring
    · rw [od_A_three, od_A_three, chi8'_mul, chi8'_eq ℓ]
      ring
  | k + 2 =>
    obtain ⟨ihe, iho⟩ := ih k (by omega)
    have h8 := chi8_sq hℓ
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rw [show k + 2 + 2 = k + 4 from rfl, ev_A_add_four, ev_A_add_four, dil_four_mul hℓ]
      unfold dil
      split_ifs
      · dsimp only
        rw [ihe]
        rw [show (ZMod.χ₈ ℓ : ℚ) ^ (k + 2) = (ZMod.χ₈ ℓ : ℚ) ^ k * (ZMod.χ₈ ℓ : ℚ) ^ 2 by ring, h8]
        ring
      · ring
    · rw [show k + 2 + 2 = k + 4 from rfl, od_A_add_four, od_A_add_four, dil_four_mul hℓ]
      unfold dil
      split_ifs
      · dsimp only
        rw [iho]
        rw [show (ZMod.χ₈ ℓ : ℚ) ^ (k + 2) = (ZMod.χ₈ ℓ : ℚ) ^ k * (ZMod.χ₈ ℓ : ℚ) ^ 2 by ring, h8]
        ring
      · ring

end MeanResidue
