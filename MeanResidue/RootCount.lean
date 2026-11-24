module

public import MeanResidue.PrimePower

@[expose] public section

/-!
# Square roots modulo prime powers: all cases

For a prime `p` (including `p = 2`):
* `cnt n a` depends only on `a` modulo `n`, and multiplying `a` by the square of a unit does not change it;
* `cnt p b = 1` when `p ∣ b`;
* `cnt (p^i) b = 0` when `i ≥ 2` and `p` divides `b` exactly once;
* `cnt (p^(i+2)) (p² b) = p · cnt (p^i) b`.

For `p = 2` and odd `u`: `cnt 2 u = 1`, `cnt 4 u = 1 + χ₄(u)`, and `cnt (2^m) u = 4` or `0` for `m ≥ 3`
according as `u ≡ 1 (mod 8)` or not. For odd `p` the unit case is `cnt_unit` (PrimePower.lean).
-/

open Finset

namespace MeanResidue

/-- `cnt n a` depends only on `a` modulo `n`. -/
theorem cnt_congr {n : ℕ} {a b : ℤ} (h : (n : ℤ) ∣ a - b) : cnt n a = cnt n b := by
  unfold cnt
  rw [(ZMod.intCast_eq_intCast_iff_dvd_sub b a n).2 h]

theorem cnt_emod (n : ℕ) (a : ℤ) : cnt n (a % n) = cnt n a :=
  cnt_congr (Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.emod_emod_of_dvd _ dvd_rfl]; simp))

/-- Multiplying by the square of a unit does not change the number of square roots. -/
theorem cnt_sq_mul {n : ℕ} {x : ℤ} (hx : IsCoprime x n) (a : ℤ) : cnt n (x ^ 2 * a) = cnt n a := by
  obtain ⟨u, v, huv⟩ := hx
  have hu : IsUnit (x : ZMod n) := by
    refine isUnit_iff_exists_inv.2 ⟨(u : ZMod n), ?_⟩
    have := congrArg (fun t : ℤ => (t : ZMod n)) huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    rw [mul_comm]; exact this
  unfold cnt
  symm
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨(hu.unit : ZMod n) * y.1, by
        rw [mul_pow, y.2, IsUnit.unit_spec]; push_cast; ring⟩
      invFun := fun y => ⟨((hu.unit⁻¹ : (ZMod n)ˣ) : ZMod n) * y.1, by
        have h2 := y.2
        push_cast at h2
        calc (((hu.unit⁻¹ : (ZMod n)ˣ) : ZMod n) * y.1) ^ 2
            = (((hu.unit⁻¹ : (ZMod n)ˣ) : ZMod n) * (x : ZMod n)) ^ 2 * (a : ZMod n) := by
              rw [mul_pow, mul_pow, h2]; ring
          _ = (a : ZMod n) := by rw [IsUnit.val_inv_mul, one_pow, one_mul]⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp only
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun y => by
        apply Subtype.ext
        simp only
        rw [← mul_assoc, Units.mul_inv, one_mul] }

/-- The count `cnt N b` as a count of `x < N`. -/
theorem cnt_eq_card_range {N : ℕ} (hN : N ≠ 0) (b : ℤ) :
    cnt N b = #{x ∈ range N | (N : ℤ) ∣ ((x : ℕ) : ℤ) ^ 2 - b} := by
  have : NeZero N := ⟨hN⟩
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply card_bij (fun x _ => x.val)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_filter, mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hx.symm
  · intro x _ y _ h
    exact ZMod.val_injective N h
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    refine ⟨(k : ZMod N), ?_, ZMod.val_natCast_of_lt hk.1⟩
    simp only [mem_filter, mem_univ, true_and]
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).2 hk.2
    push_cast at this
    exact this.symm

/-- Counting a property that is periodic modulo `M` over `k` periods. -/
theorem card_filter_range_mul {M : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ y, P (y + M) ↔ P y) (k : ℕ) :
    #{y ∈ range (k * M) | P y} = k * #{y ∈ range M | P y} := by
  have hPk : ∀ t y, P (t * M + y) ↔ P y := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro y
      rw [show (t + 1) * M + y = (t * M + y) + M by ring, hP, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [card_filter, card_filter] at *
    rw [show (k + 1) * M = k * M + M by ring, sum_range_add, ih, add_mul, one_mul]
    congr 1
    apply sum_congr rfl
    intro y _
    simp only [hPk]

variable (p : ℕ) [hp : Fact p.Prime]

/-- `cnt p b = 1` when `p ∣ b`. -/
theorem cnt_prime_of_dvd {b : ℤ} (h : (p : ℤ) ∣ b) : cnt p b = 1 := by
  unfold cnt
  have hb : (b : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).2 h
  rw [hb, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, by ring⟩, fun x => Subtype.ext ?_⟩
  exact pow_eq_zero_iff two_ne_zero |>.1 x.2

/-- No square roots modulo `p^i` (`i ≥ 2`) of a number divisible by `p` exactly once. -/
theorem cnt_pow_eq_zero {i : ℕ} (hi : 2 ≤ i) {b : ℤ} (h1 : (p : ℤ) ∣ b) (h2 : ¬ (p : ℤ) ^ 2 ∣ b) :
    cnt (p ^ i) b = 0 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rw [cnt_eq_card_range (pow_ne_zero _ hp.out.ne_zero), card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  apply h2
  push_cast at hx
  have h3 : (p : ℤ) ^ 2 ∣ (x : ℤ) ^ 2 - b := (pow_dvd_pow _ hi).trans hx
  have h4 : (p : ℤ) ∣ (x : ℤ) ^ 2 := by
    have := dvd_add ((dvd_pow_self (p : ℤ) two_ne_zero).trans h3) h1
    simpa using this
  have h6 : (p : ℤ) ^ 2 ∣ (x : ℤ) ^ 2 := pow_dvd_pow_of_dvd (hpZ.dvd_of_dvd_pow h4) 2
  have := dvd_sub h6 h3
  simpa using this

/-- **The recursion** `cnt (p^(i+2)) (p² b) = p · cnt (p^i) b`. -/
theorem cnt_pow_add_two_mul_sq (i : ℕ) (b : ℤ) :
    cnt (p ^ (i + 2)) (p ^ 2 * b) = p * cnt (p ^ i) b := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpZ0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  rw [cnt_eq_card_range (pow_ne_zero _ hp0), cnt_eq_card_range (pow_ne_zero _ hp0)]
  have step1 : #{x ∈ range (p ^ (i + 2)) | ((p ^ (i + 2) : ℕ) : ℤ) ∣ ((x : ℕ) : ℤ) ^ 2 - p ^ 2 * b} =
      #{y ∈ range (p ^ (i + 1)) | ((p ^ i : ℕ) : ℤ) ∣ ((y : ℕ) : ℤ) ^ 2 - b} := by
    symm
    apply card_bij (fun y _ => p * y)
    · intro y hy
      simp only [mem_filter, mem_range] at hy ⊢
      refine ⟨by rw [pow_succ' p (i + 1)]; exact Nat.mul_lt_mul_of_pos_left hy.1 hp.out.pos, ?_⟩
      push_cast at hy ⊢
      rw [show ((p : ℤ) * y) ^ 2 - p ^ 2 * b = p ^ 2 * (y ^ 2 - b) by ring,
        show (p : ℤ) ^ (i + 2) = p ^ 2 * p ^ i by ring]
      exact mul_dvd_mul_left _ hy.2
    · intro a _ c _ h
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos h
    · intro x hx
      simp only [mem_filter, mem_range] at hx
      push_cast at hx
      have h1 : (p : ℤ) ∣ (x : ℤ) ^ 2 := by
        have h := (dvd_pow_self (p : ℤ) (by omega : i + 2 ≠ 0)).trans hx.2
        have := dvd_add h (dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) two_ne_zero) b)
        simpa using this
      have h2 : p ∣ x := by exact_mod_cast hpZ.dvd_of_dvd_pow h1
      obtain ⟨y, rfl⟩ := h2
      refine ⟨y, ?_, rfl⟩
      simp only [mem_filter, mem_range]
      refine ⟨?_, ?_⟩
      · have := hx.1
        rw [pow_succ' p (i + 1)] at this
        exact Nat.lt_of_mul_lt_mul_left this
      · have h3 := hx.2
        push_cast at h3 ⊢
        rw [show ((p : ℤ) * y) ^ 2 - p ^ 2 * b = p ^ 2 * (y ^ 2 - b) by ring,
          show (p : ℤ) ^ (i + 2) = p ^ 2 * p ^ i by ring] at h3
        exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hpZ0)).1 h3
  rw [step1, show p ^ (i + 1) = p * p ^ i by ring, card_filter_range_mul]
  intro y
  push_cast
  rw [show ((y : ℤ) + p ^ i) ^ 2 - b = (y ^ 2 - b) + p ^ i * (2 * y + p ^ i) by ring]
  exact (dvd_add_left (dvd_mul_right _ _))

/-! ### `p = 2`, odd `u` -/

theorem cnt_two (b : ℤ) : cnt 2 b = 1 := by
  rw [← cnt_emod, Nat.cast_ofNat]
  have h : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases h with h | h <;> rw [h, cnt_eq_card_range (by norm_num)] <;> decide

theorem cnt_four_unit {u : ℤ} (hu : u % 2 = 1) : (cnt 4 u : ℤ) = 1 + ZMod.χ₄ u := by
  rw [← cnt_emod, Nat.cast_ofNat, ZMod.χ₄_int_mod_four]
  have h : u % 4 = 1 ∨ u % 4 = 3 := by omega
  rcases h with h | h <;> rw [h, cnt_eq_card_range (by norm_num)] <;> decide

/-- `x² ≡ 1 (mod 2^m)` iff `x ≡ ±1 (mod 2^(m-1))`, for `m ≥ 3`. -/
theorem two_pow_dvd_sq_sub_one {m : ℕ} (x : ℤ) :
    (2 : ℤ) ^ (m + 3) ∣ x ^ 2 - 1 ↔ (2 : ℤ) ^ (m + 2) ∣ x - 1 ∨ (2 : ℤ) ^ (m + 2) ∣ x + 1 := by
  constructor
  · intro h
    have hodd : x % 2 = 1 := by
      have h2 : (2 : ℤ) ∣ x ^ 2 - 1 := (dvd_pow_self 2 (by omega)).trans h
      rcases Int.even_or_odd' x with ⟨r, rfl | rfl⟩
      · exfalso
        rw [show (2 * r) ^ 2 - 1 = 2 * (2 * r ^ 2 - 1) + 1 by ring] at h2
        omega
      · omega
    obtain ⟨t, rfl⟩ : ∃ t, x = 2 * t + 1 := ⟨x / 2, by omega⟩
    have h4 : (2 : ℤ) ^ (m + 1) ∣ t * (t + 1) := by
      rw [show (2 * t + 1) ^ 2 - 1 = 2 ^ 2 * (t * (t + 1)) by ring,
        show (2 : ℤ) ^ (m + 3) = 2 ^ 2 * 2 ^ (m + 1) by ring] at h
      exact (mul_dvd_mul_iff_left (by norm_num)).1 h
    rcases Int.even_or_odd' t with ⟨r, rfl | rfl⟩
    · left
      have hc : IsCoprime ((2 : ℤ) ^ (m + 1)) (2 * r + 1) :=
        ((Int.prime_two.coprime_iff_not_dvd).2 (by omega)).pow_left
      have := hc.dvd_of_dvd_mul_right h4
      rw [show 2 * (2 * r) + 1 - 1 = 2 * (2 * r) by ring, pow_succ']
      exact mul_dvd_mul_left 2 this
    · right
      have hc : IsCoprime ((2 : ℤ) ^ (m + 1)) (2 * r + 1) :=
        ((Int.prime_two.coprime_iff_not_dvd).2 (by omega)).pow_left
      have := hc.dvd_of_dvd_mul_left h4
      rw [show 2 * (2 * r + 1) + 1 + 1 = 2 * (2 * r + 1 + 1) by ring, pow_succ']
      exact mul_dvd_mul_left 2 this
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · refine ⟨k * (2 ^ (m + 1) * k + 1), ?_⟩
      rw [show x = 2 ^ (m + 2) * k + 1 by linarith]
      ring
    · refine ⟨k * (2 ^ (m + 1) * k - 1), ?_⟩
      rw [show x = 2 ^ (m + 2) * k - 1 by linarith]
      ring

theorem cnt_two_pow_one (m : ℕ) : cnt (2 ^ (m + 3)) 1 = 4 := by
  rw [cnt_eq_card_range (by positivity)]
  push_cast
  simp only [two_pow_dvd_sq_sub_one]
  set M := 2 ^ (m + 2) with hM
  have hM4 : 4 ≤ M := by
    rw [hM, pow_add]; norm_num
    exact Nat.one_le_two_pow
  have hMZ : ((2 : ℤ) ^ (m + 2)) = (M : ℤ) := by rw [hM]; push_cast; ring
  rw [hMZ, show 2 ^ (m + 3) = 2 * M by rw [hM]; ring, card_filter_range_mul]
  · have hset : ({y ∈ range M | (M : ℤ) ∣ (y : ℤ) - 1 ∨ (M : ℤ) ∣ (y : ℤ) + 1} : Finset ℕ) =
        {1, M - 1} := by
      ext y
      simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hy, h | h⟩
        · left
          have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
          omega
        · right
          have h1 := Int.le_of_dvd (by omega) h
          omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, Or.inl (by simp)⟩
        · refine ⟨by omega, Or.inr ?_⟩
          rw [Nat.cast_sub (by omega)]
          simp
    rw [hset, card_pair (by omega)]
  · intro y
    push_cast
    rw [show (y : ℤ) + M - 1 = (y - 1) + M * 1 by ring, show (y : ℤ) + M + 1 = (y + 1) + M * 1 by ring,
      dvd_add_left (dvd_mul_right _ _), dvd_add_left (dvd_mul_right _ _)]

/-- Odd `u ≡ 1 (mod 8)` is a square modulo every `2^m` (Hensel's lemma at `2`). -/
theorem exists_sq_two_pow {u : ℤ} (hu : u % 8 = 1) (m : ℕ) :
    ∃ x : ℤ, x % 2 = 1 ∧ (2 : ℤ) ^ (m + 3) ∣ x ^ 2 - u := by
  induction m with
  | zero => exact ⟨1, by norm_num, Int.dvd_of_emod_eq_zero (by omega)⟩
  | succ m ih =>
    obtain ⟨x, hx, k, hk⟩ := ih
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact ⟨x, hx, j, by rw [hk]; ring⟩
    · have hpar : (x + 2 ^ (m + 2)) % 2 = 1 := by
        have : (2 : ℤ) ^ (m + 2) = 2 * (2 * 2 ^ m) := by ring
        rw [this]; omega
      refine ⟨x + 2 ^ (m + 2), hpar, ?_⟩
      obtain ⟨t, rfl⟩ : ∃ t, x = 2 * t + 1 := ⟨x / 2, by omega⟩
      refine ⟨j + t + 1 + 2 ^ m, ?_⟩
      have : (2 * t + 1 + 2 ^ (m + 2)) ^ 2 - u =
          ((2 * t + 1) ^ 2 - u) + 2 ^ (m + 3) * (2 * t + 1) + 2 ^ (2 * m + 4) := by ring
      rw [this, hk]
      ring

/-- **Odd squares modulo `2^m`** (`m ≥ 3`): an odd `u` has `4` square roots if `u ≡ 1 (mod 8)` and none
otherwise. -/
theorem cnt_two_pow_unit (m : ℕ) {u : ℤ} (hu : u % 2 = 1) :
    cnt (2 ^ (m + 3)) u = if u % 8 = 1 then 4 else 0 := by
  split_ifs with h8
  · obtain ⟨x, hx, hdvd⟩ := exists_sq_two_pow h8 m
    have hx2 : ¬ (2 : ℤ) ∣ x := by omega
    have hcop : IsCoprime x ((2 ^ (m + 3) : ℕ) : ℤ) := by
      push_cast
      exact ((Int.prime_two.coprime_iff_not_dvd).2 hx2).pow_left.symm
    rw [cnt_congr (b := x ^ 2 * 1) (by push_cast; rw [mul_one]; exact (dvd_sub_comm).1 hdvd),
      cnt_sq_mul hcop, cnt_two_pow_one]
  · unfold cnt
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨y, hy⟩ => ?_⟩
    have h8d : 8 ∣ 2 ^ (m + 3) := by rw [pow_add]; exact dvd_mul_left _ _
    have := congrArg (ZMod.castHom h8d (ZMod 8)) hy
    rw [map_pow, map_intCast, ← ZMod.intCast_mod u 8, Nat.cast_ofNat] at this
    have key : ∀ z : ZMod 8, z ^ 2 ≠ 3 ∧ z ^ 2 ≠ 5 ∧ z ^ 2 ≠ 7 := by decide
    have hu8 : u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
    rcases hu8 with h | h | h <;> rw [h] at this
    · exact (key _).1 this
    · exact (key _).2.1 this
    · exact (key _).2.2 this

/-! ### Odd `p`, integer arguments -/

theorem cnt_unit_int (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    (cnt (p ^ m) u : ℤ) = 1 + jacobiSym u p := by
  have hpm : (0 : ℤ) < ((p ^ m : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos m
  set u' := (u % ((p ^ m : ℕ) : ℤ)).toNat with hu'
  have hu'eq : (u' : ℤ) = u % ((p ^ m : ℕ) : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hpm.ne')
  have hdvd : ((p ^ m : ℕ) : ℤ) ∣ u - u' := by
    rw [hu'eq]; exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.emod_emod_of_dvd _ dvd_rfl]; simp)
  have hpdvd : (p : ℤ) ∣ u - u' := (by push_cast; exact dvd_pow_self (p : ℤ) hm : (p : ℤ) ∣ ((p ^ m : ℕ) : ℤ)).trans hdvd
  have hu'p : ¬ p ∣ u' := by
    intro h
    apply hu
    have : (p : ℤ) ∣ (u' : ℤ) := by exact_mod_cast h
    have := dvd_add hpdvd this
    simpa using this
  rw [cnt_congr hdvd, cnt_unit hp2 hm u' hu'p, jacobiSym.legendreSym.to_jacobiSym]
  congr 1
  exact jacobiSym.mod_left' (Int.emod_eq_emod_iff_emod_sub_eq_zero.2
    (Int.emod_eq_zero_of_dvd (dvd_sub_comm.1 hpdvd)))

end MeanResidue
