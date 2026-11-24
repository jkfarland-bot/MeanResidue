module

public import MeanResidue.Count

@[expose] public section

/-!
# Square roots of units modulo odd prime powers

For an odd prime `p`, `m ≥ 1` and `p ∤ u`, the number of square roots of `u` modulo `p^m` is
`1 + (u/p)`. The proof avoids Hensel's lemma: `x² = 1` only for `x = ±1`, so the squaring map on
`(ℤ/p^m)ˣ` has image of index `2`; the units whose residue mod `p` is a square also form a subgroup of
index `2` (the kernel of the quadratic character composed with reduction), containing that image;
so the two coincide.
-/

open Finset

namespace MeanResidue

variable {p : ℕ} [hp : Fact p.Prime]

/-- `x² = 1` modulo `p^m` only for `x = ±1` (odd `p`). -/
theorem sq_eq_one_iff (hp2 : p ≠ 2) (m : ℕ) (x : ZMod (p ^ m)) : x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    obtain ⟨a, rfl⟩ : ∃ a : ℤ, (a : ZMod (p ^ m)) = x := ⟨x.valMinAbs, ZMod.coe_valMinAbs x⟩
    have hdvd : ((p : ℤ) ^ m) ∣ (a - 1) * (a + 1) := by
      have : (((a - 1) * (a + 1) : ℤ) : ZMod (p ^ m)) = 0 := by
        push_cast
        linear_combination h
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
      push_cast at this
      exact this
    by_cases h1 : (p : ℤ) ∣ a - 1
    · left
      have h2 : ¬ (p : ℤ) ∣ a + 1 := by
        intro h2
        have h3 : (p : ℤ) ∣ 2 := by
          have := dvd_sub h2 h1
          rwa [show a + 1 - (a - 1) = 2 by ring] at this
        have h4 : p ∣ 2 := by exact_mod_cast h3
        rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h5 | h5
        · exact hp.out.one_lt.ne' h5
        · exact hp2 h5
      have hc : IsCoprime ((p : ℤ) ^ m) (a + 1) := ((hpZ.coprime_iff_not_dvd).2 h2).pow_left
      have h6 : ((p : ℤ) ^ m) ∣ a - 1 := hc.dvd_of_dvd_mul_right hdvd
      have : ((a - 1 : ℤ) : ZMod (p ^ m)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h6
      push_cast at this
      linear_combination this
    · right
      have hc : IsCoprime ((p : ℤ) ^ m) (a - 1) := ((hpZ.coprime_iff_not_dvd).2 h1).pow_left
      have h6 : ((p : ℤ) ^ m) ∣ a + 1 := hc.dvd_of_dvd_mul_left hdvd
      have : ((a + 1 : ℤ) : ZMod (p ^ m)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h6
      push_cast at this
      linear_combination this
  · rintro (rfl | rfl) <;> ring

/-- `1 ≠ -1` modulo `p^m` for odd `p` and `m ≥ 1`. -/
theorem one_ne_neg_one (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) : (1 : ZMod (p ^ m)) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod (p ^ m)) = 0 := by
    have : (2 : ZMod (p ^ m)) = 1 - -1 := by ring
    rw [Nat.cast_ofNat, this, ← h, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have : p ∣ 2 := (dvd_pow_self p hm).trans h2
  rcases (Nat.dvd_prime Nat.prime_two).1 this with h5 | h5
  · exact hp.out.one_lt.ne' h5
  · exact hp2 h5

/-- A residue `u` with `(u/p) = 1` is a square modulo `p^m`. -/
theorem exists_sq_of_legendre (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) (u : ℕ)
    (hu : legendreSym p u = 1) : ∃ x : ZMod (p ^ m), x ^ 2 = u := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpm : p ∣ p ^ m := dvd_pow_self p hm
  have hu0 : (u : ZMod p) ≠ 0 := by
    intro h
    rw [legendreSym, Int.cast_natCast, h, quadraticChar_zero] at hu
    exact zero_ne_one hu
  have hpu : ¬ p ∣ u := by
    rwa [Ne, ZMod.natCast_eq_zero_iff] at hu0
  have hU : IsUnit (u : ZMod (p ^ m)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp.out (Nat.pos_of_ne_zero hm)).2 hpu
  let red : (ZMod (p ^ m))ˣ →* (ZMod p)ˣ := ZMod.unitsMap hpm
  let χ : (ZMod p)ˣ →* ℤˣ := (quadraticChar (ZMod p)).toUnitHom
  let ψ : (ZMod (p ^ m))ˣ →* ℤˣ := χ.comp red
  let sq : (ZMod (p ^ m))ˣ →* (ZMod (p ^ m))ˣ := powMonoidHom 2
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  -- the image of squaring lies in the kernel of `ψ`
  have hle : sq.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    show ψ (x ^ 2) = 1
    rw [map_pow, Int.units_sq]
  -- `ψ` is onto `ℤˣ`
  have hψ : Function.Surjective ψ := by
    intro v
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
    have ha0 : a ≠ 0 := by
      intro h; rw [h, quadraticChar_zero] at ha; norm_num at ha
    obtain ⟨w, hw⟩ := ZMod.unitsMap_surjective hpm (Units.mk0 a ha0)
    rcases Int.units_eq_one_or v with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · refine ⟨w, Units.ext ?_⟩
      show ((χ (red w) : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ)
      rw [MulChar.coe_toUnitHom]
      have : (red w : ZMod p) = a := by rw [show red w = Units.mk0 a ha0 from hw]; rfl
      rw [this, ha]
      rfl
  have hkerψ : Nat.card ψ.ker * 2 = Nat.card (ZMod (p ^ m))ˣ := by
    have h2 : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    rw [← Subgroup.card_ker_mul_card_range ψ, MonoidHom.range_eq_top_of_surjective ψ hψ,
      Subgroup.card_top, h2]
  have hkersq : Nat.card sq.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, by simp⟩, ⟨-1, by simp [sq, MonoidHom.mem_ker]⟩, ?_, ?_⟩
    · intro h
      have := congrArg (fun x : sq.ker => ((x : (ZMod (p ^ m))ˣ) : ZMod (p ^ m))) h
      simp only [Units.val_one, Units.val_neg] at this
      exact one_ne_neg_one hp2 hm this
    · ext ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rw [MonoidHom.mem_ker] at hx
      have hx' : ((x : ZMod (p ^ m))) ^ 2 = 1 := by
        have := congrArg (fun y : (ZMod (p ^ m))ˣ => (y : ZMod (p ^ m))) hx
        simpa [sq] using this
      rcases (sq_eq_one_iff hp2 m _).1 hx' with h | h
      · left; ext; simp [h]
      · right; ext; simp [h]
  have hrange : Nat.card sq.range * 2 = Nat.card (ZMod (p ^ m))ˣ := by
    rw [← Subgroup.card_ker_mul_card_range sq, hkersq, mul_comm]
  have heq : sq.range = ψ.ker := by
    apply Subgroup.eq_of_le_of_card_ge hle
    omega
  have hmem : hU.unit ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    show ((χ (red hU.unit) : ℤˣ) : ℤ) = 1
    rw [MulChar.coe_toUnitHom]
    have : (red hU.unit : ZMod p) = u := by
      show ZMod.castHom hpm (ZMod p) (hU.unit : ZMod (p ^ m)) = u
      rw [IsUnit.unit_spec, map_natCast]
    rw [this]
    simpa [legendreSym] using hu
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have := congrArg (fun y : (ZMod (p ^ m))ˣ => (y : ZMod (p ^ m))) hx
  simpa [sq] using this

/-- **Square roots of a unit modulo `p^m`**: for odd `p`, `m ≥ 1` and `p ∤ u`, the number of square
roots of `u` modulo `p^m` is `1 + (u/p)`. -/
theorem cnt_unit (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) (u : ℕ) (hu : ¬ p ∣ u) :
    (cnt (p ^ m) u : ℤ) = 1 + legendreSym p u := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpm : p ∣ p ^ m := dvd_pow_self p hm
  have hu0 : ((u : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hu
  have hU : IsUnit (u : ZMod (p ^ m)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp.out (Nat.pos_of_ne_zero hm)).2 hu
  unfold cnt
  rcases legendreSym.eq_one_or_neg_one p hu0 with h | h
  · obtain ⟨x, hx⟩ := exists_sq_of_legendre hp2 hm u h
    have hxU : IsUnit x := by
      have : IsUnit (x ^ 2) := by rw [hx]; exact hU
      exact (isUnit_pow_iff two_ne_zero).1 this
    rw [h]
    have hcard : Nat.card {y : ZMod (p ^ m) // y ^ 2 = ((u : ℤ) : ZMod (p ^ m))} = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨⟨x, by rw [hx, Int.cast_natCast]⟩, ⟨-x, by rw [neg_sq, hx, Int.cast_natCast]⟩, ?_, ?_⟩
      · intro hxx
        have h1 : (1 : ZMod (p ^ m)) * x = -1 * x := by
          have := congrArg Subtype.val hxx
          simp only at this
          rw [one_mul, neg_one_mul]; exact this
        exact one_ne_neg_one hp2 hm (hxU.mul_right_cancel h1)
      · ext ⟨y, hy⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        rw [Int.cast_natCast, ← hx] at hy
        have hz : (y * ↑hxU.unit⁻¹) ^ 2 = 1 := by
          rw [mul_pow, hy, ← mul_pow, IsUnit.mul_val_inv, one_pow]
        rcases (sq_eq_one_iff hp2 m _).1 hz with hz1 | hz1
        · left
          apply Subtype.ext
          simp only
          calc y = y * ↑hxU.unit⁻¹ * x := by rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
            _ = x := by rw [hz1, one_mul]
        · right
          apply Subtype.ext
          simp only
          calc y = y * ↑hxU.unit⁻¹ * x := by rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
            _ = -x := by rw [hz1, neg_one_mul]
    rw [hcard]
    norm_num
  · rw [h]
    have hempty : IsEmpty {y : ZMod (p ^ m) // y ^ 2 = ((u : ℤ) : ZMod (p ^ m))} := by
      refine ⟨fun ⟨y, hy⟩ => ?_⟩
      have hsq : IsSquare (((u : ℤ) : ZMod p)) := by
        refine ⟨ZMod.castHom hpm (ZMod p) y, ?_⟩
        have := congrArg (ZMod.castHom hpm (ZMod p)) hy
        rw [map_pow, map_intCast] at this
        rw [← this, sq]
      have := (legendreSym.eq_one_iff p hu0).2 hsq
      rw [h] at this
      norm_num at this
    rw [Nat.card_of_isEmpty]
    norm_num

end MeanResidue
