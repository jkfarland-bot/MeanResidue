module

public import MeanResidue.Limits

@[expose] public section

/-!
# An unconditional bound for `defect n` (Weyl differencing)

`-defect n = ∑_{x ∈ ℤ/n} saw(x²)`, where `saw b = b/n - 1/2` for `b ≠ 0` and `saw 0 = 0`. Expanding `saw`
by the discrete Fourier transform on `ZMod n`,
`∑_x saw(x²) = (1/n) ∑_h 𝓕saw(h) G(h)`, `G(h) = ∑_x e(h x²/n)`.
The coefficients are explicit: `𝓕saw(0) = 0` and `𝓕saw(h) = 1/(ζ - 1) + 1/2` with `ζ = e(-h/n)`, so
`‖𝓕saw(h)‖ ≤ n/(4 min(v, n - v))` with `v = h.val`. Weyl differencing gives
`‖G(h)‖² ≤ n #{t : 2ht = 0} = n gcd(2v, n) ≤ 2n gcd(v, n)`. Summing,
`defect(n)² ≤ n^(3/2) (1 + log n)³`, with no class numbers involved.
-/

open Finset ZMod Filter Topology
open scoped ComplexConjugate

namespace MeanResidue

section Fourier

variable {n : ℕ} [NeZero n]

/-- The sawtooth on `ZMod n`: `0` at `0` and `b/n - 1/2` at `b ≠ 0` (`b` read in `[1, n)`). -/
noncomputable def saw (n : ℕ) (b : ZMod n) : ℂ := if b = 0 then 0 else (b.val : ℂ) / n - 1 / 2

/-- The quadratic Gauss sum `G(h) = ∑_x e(h x²/n)`. -/
noncomputable def qgauss (n : ℕ) [NeZero n] (h : ZMod n) : ℂ :=
  ∑ x : ZMod n, stdAddChar (h * x ^ 2)

theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ZMod n → M) :
    ∑ x : ZMod n, f x = ∑ k ∈ range n, f k := by
  symm
  apply Finset.sum_nbij' (fun k : ℕ => (k : ZMod n)) (fun x : ZMod n => x.val)
  · intros; exact mem_univ _
  · intro x _; exact mem_range.2 (ZMod.val_lt x)
  · intro k hk; exact ZMod.val_natCast_of_lt (mem_range.1 hk)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intros; rfl

omit [NeZero n] in
theorem saw_natCast {m : ℕ} (hm : m < n) :
    saw n (m : ZMod n) = if m = 0 then 0 else (m : ℂ) / n - 1 / 2 := by
  unfold saw
  have h0 : ((m : ZMod n) = 0) ↔ m = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    constructor
    · intro h; exact Nat.eq_zero_of_dvd_of_lt h hm
    · rintro rfl; exact dvd_zero _
  by_cases h : m = 0
  · rw [ite_eq_left (h0.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (h0.1 h')), ite_eq_right h, ZMod.val_natCast_of_lt hm]

/-- `-defect n = ∑_x saw(x²)`. -/
theorem neg_defect_eq_sum_saw : (-(defect n : ℚ) : ℂ) = ∑ x : ZMod n, saw n (x ^ 2) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [sum_zmod_eq_sum_range]
  have hterm : ∀ k ∈ range n, saw n ((k : ZMod n) ^ 2) =
      ((k ^ 2 % n : ℕ) : ℂ) / n - (if n ∣ k ^ 2 then 0 else 1 / 2) := by
    intro k _
    rw [show ((k : ZMod n) ^ 2) = ((k ^ 2 % n : ℕ) : ZMod n) by rw [ZMod.natCast_mod]; push_cast; ring,
      saw_natCast (Nat.mod_lt _ hn)]
    by_cases h : n ∣ k ^ 2
    · rw [ite_eq_left (Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_mod_iff dvd_rfl).2 h) (Nat.mod_lt _ hn)), ite_eq_left h,
        Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_mod_iff dvd_rfl).2 h) (Nat.mod_lt _ hn)]
      simp
    · have : k ^ 2 % n ≠ 0 := fun h' => h (Nat.dvd_of_mod_eq_zero h')
      rw [ite_eq_right this, ite_eq_right h]
  rw [sum_congr rfl hterm, sum_sub_distrib]
  have hS : ∑ k ∈ range n, ((k ^ 2 % n : ℕ) : ℂ) / n = ((S n : ℚ) : ℂ) := by
    unfold S
    push_cast
    rw [sum_div]
  have hc : ∑ k ∈ range n, (if n ∣ k ^ 2 then (0 : ℂ) else 1 / 2) = ((n : ℂ) - s n) / 2 := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have h1 := card_filter_add_card_filter_not (s := range n) (fun k => n ∣ k ^ 2)
    rw [card_range] at h1
    have h2 : (#(filter (fun k => ¬ n ∣ k ^ 2) (range n)) : ℂ) = n - s n := by
      have h1' : ((#(filter (fun k => n ∣ k ^ 2) (range n)) +
          #(filter (fun k => ¬ n ∣ k ^ 2) (range n)) : ℕ) : ℂ) = n := by exact_mod_cast h1
      push_cast at h1'
      rw [show ((s n : ℕ) : ℂ) = ((#(filter (fun k => n ∣ k ^ 2) (range n)) : ℕ) : ℂ) from rfl]
      linear_combination h1'
    rw [h2]
    ring
  rw [hS, hc]
  unfold defect
  push_cast
  ring

/-- **Fourier expansion**: `∑_x saw(x²) = (1/n) ∑_h 𝓕saw(h) G(h)`. -/
theorem sum_saw_eq_fourier :
    ∑ x : ZMod n, saw n (x ^ 2) = (n : ℂ)⁻¹ * ∑ h : ZMod n, 𝓕 (saw n) h * qgauss n h := by
  have hinv : ∀ b : ZMod n, saw n b = (n : ℂ)⁻¹ * ∑ h : ZMod n, stdAddChar (h * b) * 𝓕 (saw n) h := by
    intro b
    have := ZMod.invDFT_apply (𝓕 (saw n)) b
    rw [LinearEquiv.symm_apply_apply] at this
    rw [this, smul_eq_mul]
    simp only [smul_eq_mul]
  simp only [hinv, ← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  unfold qgauss
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  ring

/-- `(ζ - 1) ∑_{m<N} m ζ^m = N ζ^N - ζ ∑_{m<N} ζ^m`. -/
theorem arith_geom (ζ : ℂ) (N : ℕ) :
    (ζ - 1) * ∑ m ∈ range N, (m : ℂ) * ζ ^ m = N * ζ ^ N - ζ * ∑ m ∈ range N, ζ ^ m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem dft_saw_zero : 𝓕 (saw n) 0 = 0 := by
  rw [ZMod.dft_apply_zero, sum_zmod_eq_sum_range]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [sum_congr rfl (fun m hm => saw_natCast (mem_range.1 hm))]
  have h : ∀ m ∈ range n, (if m = 0 then (0 : ℂ) else (m : ℂ) / n - 1 / 2) =
      ((m : ℂ) / n - 1 / 2) + (if m = 0 then 1 / 2 else 0) := by
    intro m _
    split_ifs with h
    · subst h; simp
    · ring
  rw [sum_congr rfl h, sum_add_distrib, sum_ite_eq' (range n) 0 (fun _ => (1 / 2 : ℂ)),
    ite_eq_left (mem_range.2 hn), sum_sub_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul]
  have h2 : (∑ i ∈ range n, (i : ℂ)) * 2 = n * (n - 1) := by
    have := Finset.sum_range_id_mul_two n
    have h' : ((∑ i ∈ range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (show 1 ≤ n from hn)] at h'
    exact h'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h3 : ∑ i ∈ range n, (i : ℂ) = n * (n - 1) / 2 := by
    rw [eq_div_iff (two_ne_zero), h2]
  rw [h3]
  field_simp
  ring

/-- The Fourier coefficient of `saw` at `h ≠ 0`: `1/(ζ - 1) + 1/2` with `ζ = e(-h/n)`. -/
theorem dft_saw_ne_zero {h : ZMod n} (hh : h ≠ 0) :
    𝓕 (saw n) h = 1 / (stdAddChar (-h) - 1) + 1 / 2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set ζ : ℂ := stdAddChar (-h) with hζ
  have hζn : ζ ^ n = 1 := by
    rw [hζ, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [hζ, ← AddChar.map_zero_eq_one (stdAddChar (N := n)), injective_stdAddChar.eq_iff] at h1
    exact hh (neg_eq_zero.1 h1)
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hgeom : ∑ m ∈ range n, ζ ^ m = 0 := by
    rw [geom_sum_eq hζ1, hζn, sub_self, zero_div]
  have hag : ∑ m ∈ range n, (m : ℂ) * ζ ^ m = n / (ζ - 1) := by
    have := arith_geom ζ n
    rw [hζn, hgeom, mul_zero, sub_zero, mul_one] at this
    rw [eq_div_iff hζ1', mul_comm, this]
  rw [ZMod.dft_apply, sum_zmod_eq_sum_range]
  have hterm : ∀ m ∈ range n, stdAddChar (-((m : ZMod n) * h)) • saw n (m : ZMod n) =
      ζ ^ m * ((m : ℂ) / n - 1 / 2) + (if m = 0 then 1 / 2 else 0) := by
    intro m hm
    rw [saw_natCast (mem_range.1 hm), smul_eq_mul,
      show -((m : ZMod n) * h) = m • (-h) by rw [nsmul_eq_mul]; ring, AddChar.map_nsmul_eq_pow]
    split_ifs with h0
    · subst h0; simp
    · ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq' (range n) 0 (fun _ => (1 / 2 : ℂ)),
    ite_eq_left (mem_range.2 hn)]
  have hsplit : ∑ m ∈ range n, ζ ^ m * ((m : ℂ) / n - 1 / 2) =
      (n : ℂ)⁻¹ * ∑ m ∈ range n, (m : ℂ) * ζ ^ m - 1 / 2 * ∑ m ∈ range n, ζ ^ m := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intros
    ring
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hsplit, hag, hgeom]
  field_simp
  ring

/-- `‖𝓕saw(h)‖ ≤ 1/‖ζ - 1‖` for `h ≠ 0`, `ζ = e(-h/n)`. -/
theorem norm_dft_saw_le {h : ZMod n} (hh : h ≠ 0) :
    ‖𝓕 (saw n) h‖ ≤ 1 / ‖stdAddChar (-h) - 1‖ := by
  rw [dft_saw_ne_zero hh]
  set ζ : ℂ := stdAddChar (-h) with hζ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [hζ, ← AddChar.map_zero_eq_one (stdAddChar (N := n)), injective_stdAddChar.eq_iff] at h1
    exact hh (neg_eq_zero.1 h1)
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hnorm : ‖ζ‖ = 1 := AddChar.norm_apply _ _
  have e : 1 / (ζ - 1) + 1 / 2 = (ζ + 1) / (2 * (ζ - 1)) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul]
  have h1 : ‖ζ + 1‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hnorm, norm_one]; norm_num)
  have hpos : 0 < ‖ζ - 1‖ := norm_pos_iff.2 hζ1'
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_div_iff₀ (mul_pos two_pos hpos) hpos]
  nlinarith

/-- `‖e(-h/n) - 1‖ ≥ 4 min(v, n - v)/n` for `h ≠ 0`, `v = h.val`. -/
theorem norm_stdAddChar_sub_one {h : ZMod n} (hh : h ≠ 0) :
    4 * (min h.val (n - h.val) : ℕ) / (n : ℝ) ≤ ‖stdAddChar (-h) - 1‖ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : ‖stdAddChar (-h) - 1‖ = ‖stdAddChar h - 1‖ := by
    rw [AddChar.map_neg_eq_conj, show ∀ z : ℂ, conj z - 1 = conj (z - 1) from fun z => by simp,
      Complex.norm_conj]
  rw [h1]
  set v := h.val with hvdef
  have hv0 : v ≠ 0 := by rw [hvdef]; exact (ZMod.val_ne_zero h).2 hh
  have hvn : v < n := ZMod.val_lt h
  have hv : ((v : ℤ) : ZMod n) = h := by rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val h
  have hexp : stdAddChar h = Complex.exp (Complex.I * ((2 * Real.pi * v / n : ℝ) : ℂ)) := by
    rw [← hv, ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hvR : (0 : ℝ) < v := by exact_mod_cast Nat.pos_of_ne_zero hv0
  have hvnR : (v : ℝ) < n := by exact_mod_cast hvn
  have harg : 2 * Real.pi * v / n / 2 = Real.pi * v / n := by ring
  rw [harg]
  have hsin_pos : 0 < Real.sin (Real.pi * v / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hnR]; nlinarith [Real.pi_pos]
  rw [abs_of_pos (by linarith)]
  rcases le_total v (n - v) with hle | hle
  · rw [min_eq_left hle]
    have h2v : (2 * v : ℝ) ≤ n := by
      have : 2 * v ≤ n := by omega
      exact_mod_cast this
    have hx : Real.pi * v / n ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hnR two_pos]; nlinarith [Real.pi_pos]
    have := Real.mul_le_sin (by positivity) hx
    have e2 : 2 / Real.pi * (Real.pi * v / n) = 2 * v / n := by field_simp
    rw [e2] at this
    rw [show (4 : ℝ) * (v : ℕ) / n = 2 * (2 * v / n) by ring]
    linarith
  · rw [min_eq_right hle]
    have hsub : ((n - v : ℕ) : ℝ) = n - v := by rw [Nat.cast_sub hvn.le]
    rw [hsub]
    have h2v : (2 * (n - v) : ℝ) ≤ n := by
      have : 2 * (n - v) ≤ n := by omega
      have h' : ((2 * (n - v) : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast [Nat.cast_sub hvn.le] at h'
      linarith
    have hx : Real.pi * (n - v) / n ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hnR two_pos]; nlinarith [Real.pi_pos]
    have hx0 : 0 ≤ Real.pi * (n - v) / n := by
      apply div_nonneg _ hnR.le; nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx
    have e2 : 2 / Real.pi * (Real.pi * (n - v) / n) = 2 * (n - v) / n := by field_simp
    rw [e2] at this
    have e3 : Real.sin (Real.pi * v / n) = Real.sin (Real.pi * (n - v) / n) := by
      rw [show Real.pi * (n - v) / n = Real.pi - Real.pi * v / n by field_simp, Real.sin_pi_sub]
    rw [e3, show (4 : ℝ) * (n - v) / n = 2 * (2 * (n - v) / n) by ring]
    linarith

/-- **The coefficient bound**: `‖𝓕saw(h)‖ ≤ n/(4 min(v, n - v))` for `h ≠ 0`, `v = h.val`. -/
theorem norm_dft_saw_le' {h : ZMod n} (hh : h ≠ 0) :
    ‖𝓕 (saw n) h‖ ≤ n / (4 * (min h.val (n - h.val) : ℕ)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hv0 : h.val ≠ 0 := (ZMod.val_ne_zero h).2 hh
  have hmin : 0 < min h.val (n - h.val) := by
    have := ZMod.val_lt h
    omega
  have hminR : (0 : ℝ) < (min h.val (n - h.val) : ℕ) := by exact_mod_cast hmin
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := norm_dft_saw_le hh
  have h2 := norm_stdAddChar_sub_one hh
  have h3 : 0 < 4 * ((min h.val (n - h.val) : ℕ) : ℝ) / n := by positivity
  calc ‖𝓕 (saw n) h‖ ≤ 1 / ‖stdAddChar (-h) - 1‖ := h1
    _ ≤ 1 / (4 * ((min h.val (n - h.val) : ℕ) : ℝ) / n) := one_div_le_one_div_of_le h3 h2
    _ = n / (4 * (min h.val (n - h.val) : ℕ)) := by rw [one_div_div]

/-! ### Weyl differencing -/

/-- `‖G(h)‖² ≤ n #{t : 2ht = 0}`. -/
theorem norm_qgauss_sq (h : ZMod n) :
    ‖qgauss n h‖ ^ 2 ≤ n * #(univ.filter (fun t : ZMod n => 2 * h * t = 0)) := by
  have hconj : conj (qgauss n h) = ∑ y : ZMod n, stdAddChar (-(h * y ^ 2)) := by
    unfold qgauss
    rw [map_sum]
    apply sum_congr rfl
    intro y _
    rw [AddChar.map_neg_eq_conj]
  have hinner : ∀ y : ZMod n, ∑ x : ZMod n, stdAddChar (h * x ^ 2) * stdAddChar (-(h * y ^ 2)) =
      ∑ t : ZMod n, stdAddChar (h * t ^ 2) * stdAddChar (y * (2 * h * t)) := by
    intro y
    have hre := Fintype.sum_equiv (Equiv.addRight y)
      (fun t => stdAddChar (h * (t + y) ^ 2) * stdAddChar (-(h * y ^ 2)))
      (fun x => stdAddChar (h * x ^ 2) * stdAddChar (-(h * y ^ 2))) (fun t => rfl)
    rw [← hre]
    apply sum_congr rfl
    intro t _
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hprod : qgauss n h * conj (qgauss n h) =
      ∑ t : ZMod n, (if 2 * h * t = 0 then (n : ℂ) else 0) * stdAddChar (h * t ^ 2) := by
    rw [hconj]
    unfold qgauss
    rw [sum_mul_sum, sum_comm]
    simp only [hinner]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    rw [← mul_sum, AddChar.sum_mulShift _ (isPrimitive_stdAddChar n), ZMod.card]
    split_ifs <;> ring
  have hnorm : ‖qgauss n h‖ ^ 2 = ‖qgauss n h * conj (qgauss n h)‖ := by
    rw [norm_mul, Complex.norm_conj, sq]
  rw [hnorm, hprod]
  calc ‖∑ t : ZMod n, (if 2 * h * t = 0 then (n : ℂ) else 0) * stdAddChar (h * t ^ 2)‖
      ≤ ∑ t : ZMod n, ‖(if 2 * h * t = 0 then (n : ℂ) else 0) * stdAddChar (h * t ^ 2)‖ :=
        norm_sum_le _ _
    _ = ∑ t : ZMod n, (if 2 * h * t = 0 then (n : ℝ) else 0) := by
        apply sum_congr rfl
        intro t _
        rw [norm_mul, AddChar.norm_apply, mul_one]
        split_ifs <;> simp
    _ = n * #(univ.filter (fun t : ZMod n => 2 * h * t = 0)) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

end Fourier

/-! ### Counting -/

/-- `#{m < n : n ∣ a m} = gcd(a, n)`. -/
theorem card_dvd_mul (a : ℕ) {n : ℕ} (hn : 0 < n) :
    #{m ∈ range n | n ∣ a * m} = Nat.gcd a n := by
  set g := Nat.gcd a n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right a hn
  obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_right a n
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left a n
  have hcop : Nat.Coprime a' n' := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) hg0
    rw [← hg] at this
    rwa [ha', hn', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hn'0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h, mul_zero] at hn'; omega
    · exact h
  have hiff : ∀ m, n ∣ a * m ↔ n' ∣ m := by
    intro m
    rw [hn', ha', mul_assoc, Nat.mul_dvd_mul_iff_left hg0]
    exact hcop.symm.dvd_mul_left
  rw [filter_congr (fun m _ => hiff m), hn', mul_comm g n', show n' * g = g * n' by ring,
    card_filter_range_mul (fun m => n' ∣ m) (fun y => Nat.dvd_add_self_right) g]
  have h1 : ({m ∈ range n' | n' ∣ m} : Finset ℕ) = {0} := by
    ext m
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact Nat.eq_zero_of_dvd_of_lt h2 h1
    · rintro rfl; exact ⟨hn'0, dvd_zero _⟩
  rw [h1, card_singleton, mul_one]

theorem card_zmod_mul_eq_zero {n : ℕ} [NeZero n] (c : ZMod n) :
    #(univ.filter (fun t : ZMod n => c * t = 0)) = Nat.gcd c.val n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← card_dvd_mul c.val hn, card_filter, card_filter, sum_zmod_eq_sum_range]
  apply sum_congr rfl
  intro m _
  have : c * (m : ZMod n) = 0 ↔ n ∣ c.val * m := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp only [this]

theorem gcd_two_mul_le {n : ℕ} [NeZero n] (h : ZMod n) :
    Nat.gcd (2 * h).val n ≤ 2 * Nat.gcd h.val n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmod : (2 * h).val ≡ 2 * h.val [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val]
    norm_num
  rw [Nat.ModEq.gcd_eq hmod]
  apply Nat.le_of_dvd (Nat.mul_pos two_pos (Nat.gcd_pos_of_pos_right _ hn))
  rw [← Nat.gcd_mul_left]
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left n 2))

/-- `‖G(h)‖² ≤ 2 n gcd(v, n)`. -/
theorem norm_qgauss_sq_le {n : ℕ} [NeZero n] (h : ZMod n) :
    ‖qgauss n h‖ ^ 2 ≤ 2 * n * Nat.gcd h.val n := by
  have h1 := norm_qgauss_sq h
  rw [card_zmod_mul_eq_zero] at h1
  have h2 : (Nat.gcd (2 * h).val n : ℝ) ≤ 2 * Nat.gcd h.val n := by exact_mod_cast gcd_two_mul_le h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith


/-! ### The arithmetic sum -/

/-- `∑_{d ∣ n} 1/d ≤ 1 + log n`. -/
theorem sum_inv_divisors_le (n : ℕ) : ∑ d ∈ n.divisors, (1 : ℝ) / d ≤ 1 + Real.log n := by
  calc ∑ d ∈ n.divisors, (1 : ℝ) / d ≤ ∑ d ∈ Icc 1 n, (1 : ℝ) / d := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
        · intros
          positivity
    _ = (harmonic n : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp [one_div]
    _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

/-- `∑_{v < n, g ∣ v, v ≥ 1} 1/v ≤ (1/g)(1 + log n)`. -/
theorem sum_multiples_inv_le {g : ℕ} (hg : 0 < g) (n : ℕ) :
    ∑ v ∈ (Ico 1 n).filter (g ∣ ·), (1 : ℝ) / v ≤ (1 / g) * (1 + Real.log n) := by
  have hinj : Set.InjOn (fun v => v / g) ↑((Ico 1 n).filter (g ∣ ·)) := by
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    have := congrArg (· * g) hab
    simp only at this
    rwa [Nat.div_mul_cancel ha.2, Nat.div_mul_cancel hb.2] at this
  have hsum : ∑ v ∈ (Ico 1 n).filter (g ∣ ·), (1 : ℝ) / v =
      ∑ m ∈ ((Ico 1 n).filter (g ∣ ·)).image (fun v => v / g), (1 : ℝ) / (g * m) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro v hv
    rw [mem_filter] at hv
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hv.2]
  have hsub : ((Ico 1 n).filter (g ∣ ·)).image (fun v => v / g) ⊆ Icc 1 n := by
    intro m hm
    simp only [mem_image, mem_filter, mem_Ico] at hm
    obtain ⟨v, ⟨⟨hv1, hvn⟩, hgv⟩, rfl⟩ := hm
    rw [mem_Icc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hgv) hg
    · exact (Nat.div_le_self v g).trans hvn.le
  rw [hsum]
  calc ∑ m ∈ ((Ico 1 n).filter (g ∣ ·)).image (fun v => v / g), (1 : ℝ) / (g * m)
      ≤ ∑ m ∈ Icc 1 n, (1 : ℝ) / (g * m) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (1 / g) * ∑ m ∈ Icc 1 n, (1 : ℝ) / m := by
        rw [mul_sum]
        apply sum_congr rfl
        intros
        rw [one_div_mul_one_div]
    _ ≤ (1 / g) * (1 + Real.log n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ m ∈ Icc 1 n, (1 : ℝ) / m = (harmonic n : ℝ) := by
              rw [harmonic_eq_sum_Icc]
              push_cast
              simp [one_div]
          _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

/-- `∑_{1 ≤ v < n} √gcd(v, n)/v ≤ (1 + log n) ∑_{g ∣ n} 1/√g`. -/
theorem sum_sqrt_gcd_le (n : ℕ) (hn : 0 < n) :
    ∑ v ∈ Ico 1 n, Real.sqrt (Nat.gcd v n) / v ≤
      (1 + Real.log n) * ∑ g ∈ n.divisors, 1 / Real.sqrt g := by
  have h1 : ∀ v ∈ Ico 1 n, Real.sqrt (Nat.gcd v n) / v ≤
      ∑ g ∈ n.divisors, (if g ∣ v then Real.sqrt g / v else 0) := by
    intro v _
    have hmem : Nat.gcd v n ∈ n.divisors :=
      Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right v n, hn.ne'⟩
    have := single_le_sum (f := fun g => if g ∣ v then Real.sqrt g / v else (0 : ℝ))
      (fun g _ => by split_ifs <;> positivity) hmem
    simp only [ite_eq_left (Nat.gcd_dvd_left v n)] at this
    exact this
  calc ∑ v ∈ Ico 1 n, Real.sqrt (Nat.gcd v n) / v
      ≤ ∑ v ∈ Ico 1 n, ∑ g ∈ n.divisors, (if g ∣ v then Real.sqrt g / v else 0) := sum_le_sum h1
    _ = ∑ g ∈ n.divisors, Real.sqrt g * ∑ v ∈ (Ico 1 n).filter (g ∣ ·), (1 : ℝ) / v := by
        rw [sum_comm]
        apply sum_congr rfl
        intro g _
        rw [sum_filter, mul_sum]
        apply sum_congr rfl
        intros
        split_ifs <;> ring
    _ ≤ ∑ g ∈ n.divisors, Real.sqrt g * ((1 / g) * (1 + Real.log n)) := by
        apply sum_le_sum
        intro g hg
        exact mul_le_mul_of_nonneg_left (sum_multiples_inv_le (Nat.pos_of_mem_divisors hg) n)
          (Real.sqrt_nonneg _)
    _ = (1 + Real.log n) * ∑ g ∈ n.divisors, 1 / Real.sqrt g := by
        rw [mul_sum]
        apply sum_congr rfl
        intro g hg
        have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_mem_divisors hg
        rw [show Real.sqrt g * ((1 / g) * (1 + Real.log n)) = (1 + Real.log n) * (Real.sqrt g / g) by ring,
          Real.sqrt_div_self']

/-- `(∑_{g ∣ n} 1/√g)² ≤ 2 √n (1 + log n)`. -/
theorem sum_inv_sqrt_divisors_sq (n : ℕ) :
    (∑ g ∈ n.divisors, 1 / Real.sqrt g) ^ 2 ≤ 2 * Real.sqrt n * (1 + Real.log n) := by
  have h := sum_mul_sq_le_sq_mul_sq n.divisors (fun _ => (1 : ℝ)) (fun g => 1 / Real.sqrt g)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
  have e : ∑ g ∈ n.divisors, (1 / Real.sqrt g) ^ 2 = ∑ g ∈ n.divisors, (1 : ℝ) / g := by
    apply sum_congr rfl
    intros
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [e] at h
  calc (∑ g ∈ n.divisors, 1 / Real.sqrt g) ^ 2 ≤ (#n.divisors : ℝ) * ∑ g ∈ n.divisors, (1 : ℝ) / g := h
    _ ≤ 2 * Real.sqrt n * (1 + Real.log n) :=
        mul_le_mul (card_divisors_le_two_sqrt n) (sum_inv_divisors_le n)
          (sum_nonneg (fun _ _ => by positivity)) (by positivity)

/-- Reflection: `∑_{1 ≤ v < n} √gcd(v, n)/(n - v) = ∑_{1 ≤ v < n} √gcd(v, n)/v`. -/
theorem sum_sqrt_gcd_reflect (n : ℕ) :
    ∑ v ∈ Ico 1 n, Real.sqrt (Nat.gcd v n) / ((n - v : ℕ) : ℝ) =
      ∑ v ∈ Ico 1 n, Real.sqrt (Nat.gcd v n) / v := by
  have h := sum_Ico_reflect (fun x => Real.sqrt (Nat.gcd x n) / (x : ℝ)) 1 (show n ≤ n + 1 by omega)
  simp only [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega] at h
  rw [← h]
  apply sum_congr rfl
  intro v hv
  rw [mem_Ico] at hv
  rw [Nat.gcd_self_sub_left hv.2.le]

/-! ### The bound -/

theorem one_div_min_le {v n : ℕ} (hv : 0 < v) (hvn : v < n) :
    (1 : ℝ) / (min v (n - v) : ℕ) ≤ 1 / v + 1 / ((n - v : ℕ) : ℝ) := by
  have h1 : (0 : ℝ) < v := by exact_mod_cast hv
  have h2 : (0 : ℝ) < ((n - v : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - v by omega)
  rcases le_total v (n - v) with h | h
  · rw [min_eq_left h]; linarith [one_div_pos.2 h2]
  · rw [min_eq_right h]; linarith [one_div_pos.2 h1]

/-- **The unconditional bound**: `defect(n)² ≤ n √n (1 + log n)³`. -/
theorem defect_sq_le (n : ℕ) (hn : 0 < n) :
    ((defect n : ℚ) : ℝ) ^ 2 ≤ n * Real.sqrt n * (1 + Real.log n) ^ 3 := by
  have : NeZero n := ⟨hn.ne'⟩
  set L : ℝ := 1 + Real.log n with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set A : ℝ := ∑ v ∈ Ico 1 n, Real.sqrt (Nat.gcd v n) / v with hA
  -- the term bound for `1 ≤ v < n`
  have hterm : ∀ v ∈ Ico 1 n, ‖𝓕 (saw n) (v : ZMod n)‖ * ‖qgauss n (v : ZMod n)‖ ≤
      (n / 4 * Real.sqrt (2 * n)) * (Real.sqrt (Nat.gcd v n) / v +
        Real.sqrt (Nat.gcd v n) / ((n - v : ℕ) : ℝ)) := by
    intro v hv
    rw [mem_Ico] at hv
    have hval : (v : ZMod n).val = v := ZMod.val_natCast_of_lt hv.2
    have hne : (v : ZMod n) ≠ 0 := by
      intro h0
      have := congrArg ZMod.val h0
      rw [hval, ZMod.val_zero] at this
      omega
    have hF := norm_dft_saw_le' hne
    rw [hval] at hF
    have hG : ‖qgauss n (v : ZMod n)‖ ≤ Real.sqrt (2 * n) * Real.sqrt (Nat.gcd v n) := by
      rw [← Real.sqrt_mul (by positivity)]
      have h2 := norm_qgauss_sq_le (v : ZMod n)
      rw [hval] at h2
      have := Real.abs_le_sqrt h2
      rwa [abs_norm] at this
    have hmin := one_div_min_le (show 0 < v by omega) hv.2
    have hminpos : (0 : ℝ) < (min v (n - v) : ℕ) := by
      exact_mod_cast (show 0 < min v (n - v) by omega)
    have hF' : ‖𝓕 (saw n) (v : ZMod n)‖ ≤ n / 4 * (1 / v + 1 / ((n - v : ℕ) : ℝ)) := by
      calc ‖𝓕 (saw n) (v : ZMod n)‖ ≤ n / (4 * (min v (n - v) : ℕ)) := hF
        _ = n / 4 * (1 / (min v (n - v) : ℕ)) := by field_simp
        _ ≤ n / 4 * (1 / v + 1 / ((n - v : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hmin (by positivity)
    calc ‖𝓕 (saw n) (v : ZMod n)‖ * ‖qgauss n (v : ZMod n)‖
        ≤ (n / 4 * (1 / v + 1 / ((n - v : ℕ) : ℝ))) *
            (Real.sqrt (2 * n) * Real.sqrt (Nat.gcd v n)) :=
          mul_le_mul hF' hG (norm_nonneg _) (by
            have : (0 : ℝ) < ((n - v : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - v by omega)
            positivity)
      _ = (n / 4 * Real.sqrt (2 * n)) * (Real.sqrt (Nat.gcd v n) / v +
            Real.sqrt (Nat.gcd v n) / ((n - v : ℕ) : ℝ)) := by ring
  -- `|defect n| ≤ √(2n) A / 2`
  have hD : |((defect n : ℚ) : ℝ)| ≤ Real.sqrt (2 * n) * A / 2 := by
    have h0 := neg_defect_eq_sum_saw (n := n)
    rw [sum_saw_eq_fourier] at h0
    have hnorm : |((defect n : ℚ) : ℝ)| = ‖(n : ℂ)⁻¹ * ∑ h : ZMod n, 𝓕 (saw n) h * qgauss n h‖ := by
      rw [← h0, norm_neg, Complex.norm_ratCast]
    rw [hnorm, norm_mul, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ h : ZMod n, 𝓕 (saw n) h * qgauss n h‖ ≤
        (n / 4 * Real.sqrt (2 * n)) * (2 * A) := by
      calc ‖∑ h : ZMod n, 𝓕 (saw n) h * qgauss n h‖
          ≤ ∑ h : ZMod n, ‖𝓕 (saw n) h‖ * ‖qgauss n h‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            apply sum_congr rfl
            intros
            rw [norm_mul]
        _ = ∑ v ∈ range n, ‖𝓕 (saw n) (v : ZMod n)‖ * ‖qgauss n (v : ZMod n)‖ :=
            sum_zmod_eq_sum_range (fun h => ‖𝓕 (saw n) h‖ * ‖qgauss n h‖)
        _ = ∑ v ∈ Ico 1 n, ‖𝓕 (saw n) (v : ZMod n)‖ * ‖qgauss n (v : ZMod n)‖ := by
            rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
            simp [dft_saw_zero]
        _ ≤ ∑ v ∈ Ico 1 n, (n / 4 * Real.sqrt (2 * n)) * (Real.sqrt (Nat.gcd v n) / v +
              Real.sqrt (Nat.gcd v n) / ((n - v : ℕ) : ℝ)) := sum_le_sum hterm
        _ = (n / 4 * Real.sqrt (2 * n)) * (2 * A) := by
            rw [← mul_sum, sum_add_distrib, sum_sqrt_gcd_reflect, hA]
            ring
    calc (n : ℝ)⁻¹ * ‖∑ h : ZMod n, 𝓕 (saw n) h * qgauss n h‖
        ≤ (n : ℝ)⁻¹ * ((n / 4 * Real.sqrt (2 * n)) * (2 * A)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.sqrt (2 * n) * A / 2 := by
          field_simp
          ring
  -- `A ≤ L B` and `B² ≤ 2 √n L`
  set B : ℝ := ∑ g ∈ n.divisors, 1 / Real.sqrt g with hB
  have hA0 : 0 ≤ A := sum_nonneg (fun _ _ => by positivity)
  have hAB : A ≤ L * B := sum_sqrt_gcd_le n hn
  have hB2 : B ^ 2 ≤ 2 * Real.sqrt n * L := sum_inv_sqrt_divisors_sq n
  have hsq2 : Real.sqrt (2 * n) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  calc ((defect n : ℚ) : ℝ) ^ 2 = |((defect n : ℚ) : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (2 * n) * A / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hD 2
    _ = n / 2 * A ^ 2 := by rw [div_pow, mul_pow, hsq2]; ring
    _ ≤ n / 2 * (L * B) ^ 2 := by gcongr
    _ = n / 2 * L ^ 2 * B ^ 2 := by ring
    _ ≤ n / 2 * L ^ 2 * (2 * Real.sqrt n * L) := by gcongr
    _ = n * Real.sqrt n * L ^ 3 := by ring


/-- `(defect n / n)² ≤ 729 n^(-1/8)`. -/
theorem defect_div_sq_le {n : ℕ} (hn : 0 < n) :
    ((defect n : ℝ) / n) ^ 2 ≤ 729 * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  set x : ℝ := (n : ℝ) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hD2 := defect_sq_le n hn
  rw [← hxdef] at hD2
  set L : ℝ := 1 + Real.log x with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    linarith
  have hL3 : L ^ 3 ≤ 729 * x ^ (3 / 8 : ℝ) := by
    have h := one_add_log_le hx1
    calc L ^ 3 ≤ (9 * x ^ (1 / 8 : ℝ)) ^ 3 := pow_le_pow_left₀ (by linarith) h 3
      _ = 729 * x ^ (3 / 8 : ℝ) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
          norm_num
  have hpow : x ^ (-(1 / 8 : ℝ)) = Real.sqrt x * x ^ (3 / 8 : ℝ) / x := by
    rw [eq_div_iff hx0.ne', Real.sqrt_eq_rpow, ← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']
    norm_num
  rw [div_pow, hpow]
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  rw [div_le_iff₀ hx2]
  calc (defect n : ℝ) ^ 2 ≤ x * Real.sqrt x * L ^ 3 := hD2
    _ ≤ x * Real.sqrt x * (729 * x ^ (3 / 8 : ℝ)) := by gcongr
    _ = 729 * (Real.sqrt x * x ^ (3 / 8 : ℝ) / x) * x ^ 2 := by
        field_simp

/-- **`defect n = o(n)`, unconditionally.** -/
theorem defect_div_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (defect n : ℝ) / n) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun n : ℕ => Real.sqrt (729 * (n : ℝ) ^ (-(1 / 8 : ℝ))))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    simpa using (h1.const_mul 729).sqrt
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (defect_div_sq_le hn)

/-- **Conjecture 7.5 of Chamberland and Dilcher** (with the fourth limit read as `f(4n+3)/(4n+3)`):
`f(n)/n → 1/8, 0, -1/8, -1/4` as `n → ∞` through `n ≡ 0, 1, 2, 3 (mod 4)`. -/
theorem conj_7_5 :
    Tendsto (fun k : ℕ => (f (4 * k) : ℝ) / (4 * k : ℕ)) atTop (𝓝 (1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 1) : ℝ) / (4 * k + 1 : ℕ)) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 2) : ℝ) / (4 * k + 2 : ℕ)) atTop (𝓝 (-1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 3) : ℝ) / (4 * k + 3 : ℕ)) atTop (𝓝 (-1 / 4)) :=
  limits_of_defect_div_tendsto defect_div_tendsto_zero

end MeanResidue
