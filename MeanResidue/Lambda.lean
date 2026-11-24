module

public import MeanResidue.Phi
public import MeanResidue.Conjectures

@[expose] public section

/-!
# The sawtooth functional and the divisor form of Theorem 1.1 for every `n ≥ 1`

`Lam d g = -(1/d) ∑_{0<b<d} g(b) (b - d/2)` (a finite sawtooth sum). Then:
* `defect n = Lam n (cnt n ·)` (from `defect_mul`);
* `Lam` is unchanged when a function periodic modulo `m` is viewed modulo a multiple of `m`
  (`Lam_inflate`) and under the dilation `g ↦ [q ∣ b] g(b/q)` from level `m` to level `q m`
  (`Lam_dilate`); it vanishes on even functions (`Lam_even`).

With `cnt n = ∑_{d ∣ n} phi d` this gives, for every `n ≥ 1`,
`defect n = ∑_{d ∣ n} G d`, where `G d = Lam d (phi d ·)` (`defect_eq_sum_G`), and `G d = 0` for
`d ≡ 1, 2 (mod 4)`.
-/

open Finset

namespace MeanResidue

/-- The sawtooth functional `Lam d g = -(1/d) ∑_{0<b<d} g(b) (b - d/2)`. -/
def Lam (d : ℕ) (g : ℤ → ℚ) : ℚ := -(∑ b ∈ Ico 1 d, g b * ((b : ℚ) - d / 2)) / d

theorem Lam_congr {d : ℕ} {g h : ℤ → ℚ} (hgh : ∀ b : ℕ, 0 < b → b < d → g b = h b) :
    Lam d g = Lam d h := by
  unfold Lam
  congr 2
  apply sum_congr rfl
  intro b hb
  rw [mem_Ico] at hb
  rw [hgh b (by omega) hb.2]

theorem Lam_add (d : ℕ) (g h : ℤ → ℚ) : Lam d (fun b => g b + h b) = Lam d g + Lam d h := by
  unfold Lam
  rw [← add_div, ← neg_add, ← sum_add_distrib]
  congr 2
  apply sum_congr rfl
  intros
  ring

theorem Lam_smul (d : ℕ) (c : ℚ) (g : ℤ → ℚ) : Lam d (fun b => c * g b) = c * Lam d g := by
  unfold Lam
  have : ∑ b ∈ Ico 1 d, c * g b * ((b : ℚ) - d / 2) = c * ∑ b ∈ Ico 1 d, g b * ((b : ℚ) - d / 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [this]
  ring

theorem Lam_sub (d : ℕ) (g h : ℤ → ℚ) : Lam d (fun b => g b - h b) = Lam d g - Lam d h := by
  have := Lam_add d g (fun b => (-1) * h b)
  rw [Lam_smul] at this
  simp only [neg_one_mul, ← sub_eq_add_neg] at this
  exact this

theorem Lam_zero (d : ℕ) : Lam d (fun _ => 0) = 0 := by
  simp [Lam]

theorem Lam_sum {ι : Type*} (s : Finset ι) (d : ℕ) (g : ι → ℤ → ℚ) :
    Lam d (fun b => ∑ i ∈ s, g i b) = ∑ i ∈ s, Lam d (g i) := by
  unfold Lam
  simp only [sum_mul]
  rw [sum_comm, ← sum_neg_distrib, sum_div]

/-- `Lam` over a full period. -/
theorem Lam_eq_range {d : ℕ} (hd : 0 < d) (g : ℤ → ℚ) :
    Lam d g = -(∑ b ∈ range d, (b : ℚ) * g b) / d + ((∑ b ∈ range d, g b) - g 0) / 2 := by
  have h1 := range_split d hd (fun b => (b : ℚ) * g b)
  have h2 := range_split d hd (fun b => g b)
  simp only [Nat.cast_zero, zero_mul, zero_add] at h1 h2
  have h3 : ∑ b ∈ Ico 1 d, g b * ((b : ℚ) - d / 2) =
      ∑ b ∈ Ico 1 d, (b : ℚ) * g b - d / 2 * ∑ b ∈ Ico 1 d, g b := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intros
    ring
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold Lam
  rw [h3, h1, h2]
  field_simp
  ring

theorem periodic_nat {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (t : ℕ) (b : ℤ) :
    g (b + m * t) = g b := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show b + (m : ℤ) * ((t + 1 : ℕ) : ℤ) = (b + m * t) + m by push_cast; ring, hg, ih]

/-- Block sums of a periodic function. -/
theorem sum_range_periodic {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (t : ℕ) :
    ∑ b ∈ range (m * t), g b = t * ∑ b ∈ range m, g b ∧
      ∑ b ∈ range (m * t), (b : ℚ) * g b =
        t * ∑ b ∈ range m, (b : ℚ) * g b + m * (t * (t - 1) / 2) * ∑ b ∈ range m, g b := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hshift : ∀ x : ℕ, g ((m * t + x : ℕ) : ℤ) = g x := by
      intro x
      rw [show ((m * t + x : ℕ) : ℤ) = (x : ℤ) + m * t by push_cast; ring, periodic_nat hg]
    rw [show m * (t + 1) = m * t + m by ring, sum_range_add, sum_range_add, ih.1, ih.2]
    simp only [hshift]
    constructor
    · push_cast
      ring
    · have : ∑ x ∈ range m, ((m * t + x : ℕ) : ℚ) * g x =
          (m * t : ℚ) * ∑ x ∈ range m, g x + ∑ x ∈ range m, (x : ℚ) * g x := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intros
        push_cast
        ring
      rw [this]
      push_cast
      ring

/-- **Inflation**: a function periodic modulo `m` has the same `Lam` at level `m t`. -/
theorem Lam_inflate {m t : ℕ} (hm : 0 < m) (ht : 0 < t) {g : ℤ → ℚ}
    (hg : ∀ b, g (b + m) = g b) : Lam (m * t) g = Lam m g := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Lam_eq_range (Nat.mul_pos hm ht), Lam_eq_range hm, (sum_range_periodic hg t).1,
    (sum_range_periodic hg t).2]
  push_cast
  field_simp
  ring

/-- **Dilation**: `Lam (q m) ([q ∣ b] g(b/q)) = Lam m g`. -/
theorem Lam_dilate {q m : ℕ} (hq : 0 < q) (g : ℤ → ℚ) :
    Lam (q * m) (fun b => if (q : ℤ) ∣ b then g (b / q) else 0) = Lam m g := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have himg : (Ico 1 m).image (fun c => q * c) ⊆ Ico 1 (q * m) := by
    intro b hb
    simp only [mem_image, mem_Ico] at hb ⊢
    obtain ⟨c, hc, rfl⟩ := hb
    constructor
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hq.ne' (by omega))
    · exact Nat.mul_lt_mul_of_pos_left hc.2 hq
  have hzero : ∀ b ∈ Ico 1 (q * m), b ∉ (Ico 1 m).image (fun c => q * c) →
      (if (q : ℤ) ∣ (b : ℤ) then g ((b : ℤ) / q) else 0) * ((b : ℚ) - ↑(q * m) / 2) = 0 := by
    intro b hb hnot
    rw [mem_Ico] at hb
    rw [ite_eq_right (fun h => ?_), zero_mul]
    obtain ⟨c, hc⟩ : q ∣ b := by exact_mod_cast h
    apply hnot
    rw [mem_image]
    refine ⟨c, ?_, hc.symm⟩
    rw [mem_Ico]
    constructor
    · rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc; omega
      · exact h0
    · rw [hc] at hb
      exact Nat.lt_of_mul_lt_mul_left hb.2
  unfold Lam
  rw [← sum_subset himg hzero, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  have : ∀ c ∈ Ico 1 m, (if (q : ℤ) ∣ ((q * c : ℕ) : ℤ) then g (((q * c : ℕ) : ℤ) / q) else 0) *
      (((q * c : ℕ) : ℚ) - ↑(q * m) / 2) = q * (g c * ((c : ℚ) - m / 2)) := by
    intro c _
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [ite_eq_left (by push_cast; exact dvd_mul_right _ _)]
    push_cast
    rw [Int.mul_ediv_cancel_left _ hq0]
    ring
  rw [sum_congr rfl this, ← mul_sum, Nat.cast_mul, neg_div, neg_div,
    mul_div_mul_left _ _ hqQ]

/-- **Even functions**: `Lam m g = 0` if `g` is periodic modulo `m` and even. -/
theorem Lam_even {m : ℕ} {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (he : ∀ b, g (-b) = g b) :
    Lam m g = 0 := by
  have h := sum_Ico_reflect (fun x => g x * ((x : ℚ) - m / 2)) 1 (show m ≤ m + 1 by omega)
  simp only [show m + 1 - m = 1 by omega, show m + 1 - 1 = m by omega] at h
  have h2 : ∑ b ∈ Ico 1 m, g ((m - b : ℕ) : ℤ) * (((m - b : ℕ) : ℚ) - m / 2) =
      -∑ b ∈ Ico 1 m, g b * ((b : ℚ) - m / 2) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro b hb
    rw [mem_Ico] at hb
    have : g ((m - b : ℕ) : ℤ) = g b := by
      rw [show ((m - b : ℕ) : ℤ) = -(b : ℤ) + m by push_cast [Nat.cast_sub hb.2.le]; ring, hg, he]
    rw [this]
    push_cast [Nat.cast_sub hb.2.le]
    ring
  unfold Lam
  rw [h2] at h
  have : ∑ b ∈ Ico 1 m, g b * ((b : ℚ) - m / 2) = 0 := by linarith
  rw [this]
  simp

/-! ### Theorem 1.1 in divisor form -/

/-- `defect n` as a sawtooth sum of the root counts. -/
theorem defect_eq_Lam {n : ℕ} (hn : 0 < n) : defect n = Lam n (fun b => (cnt n b : ℚ)) := by
  have h := defect_mul n hn
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Lam
  rw [eq_div_iff hnQ, mul_comm, h]
  congr 1
  apply sum_congr rfl
  intro b hb
  rw [mem_Ico] at hb
  dsimp only
  rw [cR, cnt_eq_card n b hn hb.2]

/-- The contribution of the divisor `d`: `G d = Lam d (phi d ·)`. -/
noncomputable def G (d : ℕ) : ℚ := Lam d (fun b => (phi d b : ℚ))

theorem phi_periodic (d : ℕ) (b : ℤ) : (phi d (b + d) : ℚ) = phi d b := by
  have := phi_add_mul d b 1
  rw [mul_one] at this
  rw [this]

/-- **Theorem 1.1, divisor form, for every `n ≥ 1`**: `(n - s(n))/2 - S n = ∑_{d ∣ n} G d`. -/
theorem defect_eq_sum_G {n : ℕ} (hn : 0 < n) : defect n = ∑ d ∈ n.divisors, G d := by
  rw [defect_eq_Lam hn]
  have h : (fun b => (cnt n b : ℚ)) = fun b => ∑ d ∈ n.divisors, (phi d b : ℚ) := by
    funext b
    exact_mod_cast cnt_eq_sum_phi hn.ne' b
  rw [h, Lam_sum]
  apply sum_congr rfl
  intro d hd
  obtain ⟨t, ht⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at ht; omega
    · exact h0
  unfold G
  rw [ht]
  exact Lam_inflate hd0 ht0 (phi_periodic d)

/-- **Möbius-inverted form** (Corollary 1.3(d)): `∑_{d ∣ n} μ(n/d) defect(d) = G n`. -/
theorem moebius_defect {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℚ) * defect d = G n := by
  rw [← moebius_inversion G hn]
  apply sum_congr rfl
  intro d hd
  rw [defect_eq_sum_G (Nat.pos_of_mem_divisors hd)]

/-- `G d = 0` for `d ≡ 2 (mod 4)`. -/
theorem G_two_mod_four {d : ℕ} (h : d % 4 = 2) : G d = 0 := by
  have hd : d = 2 * (d / 2) := by omega
  have hcop : Nat.Coprime 2 (d / 2) := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.2 (by omega)
  unfold G
  rw [← Lam_zero d]
  apply Lam_congr
  intro b _ _
  rw [hd, phi_mul hcop, phi_two, zero_mul]
  rfl

/-- `G d = 0` for `d ≡ 1 (mod 4)`. -/
theorem G_one_mod_four {d : ℕ} (h : d % 4 = 1) : G d = 0 := by
  have hd : Odd d := Nat.odd_iff.2 (by omega)
  apply Lam_even (phi_periodic d)
  intro b
  rw [phi_neg hd, ZMod.χ₄_nat_one_mod_four h, one_mul]

/-- **Odd `n`**: `defect n = ∑_{d ∣ n, d ≡ 3 (mod 4)} G d`. -/
theorem defect_odd {n : ℕ} (hn : Odd n) :
    defect n = ∑ d ∈ n.divisors with d % 4 = 3, G d := by
  have hn0 : 0 < n := hn.pos
  rw [defect_eq_sum_G hn0, sum_filter]
  apply sum_congr rfl
  intro d hd
  have hdo : Odd d := Odd.of_dvd_nat hn (Nat.dvd_of_mem_divisors hd)
  have : d % 4 = 1 ∨ d % 4 = 3 := by
    rcases hdo with ⟨k, rfl⟩
    omega
  rcases this with h | h
  · rw [G_one_mod_four h, ite_eq_right (by omega)]
  · rw [ite_eq_left h]

end MeanResidue
