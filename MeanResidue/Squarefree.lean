module

public import MeanResidue.Count

@[expose] public section

/-!
# The mean residue at odd squarefree `n` (Theorem 1.1 in Bernoulli form)

For odd squarefree `n`,
`defect n = (n - 1)/2 - S n = ∑_{d ∣ n, d ≡ 3 (mod 4)} hB d`,
where `hB d = -(1/d) ∑_{a<d} a (a/d)`. With Dirichlet's class number formula `hB d = h*(-d)`
(quoted, not formalized) this is Theorem 1.1 of the paper for odd squarefree `n`.

The proof: the number of `k` with `k² ≡ b (mod n)` is `∑_{d ∣ n} (b/d)`; pairing `b` with `n - b`
kills the divisors `d ≡ 1 (mod 4)`, and for `d ≡ 3 (mod 4)` the sum over a period of `(·/d)` is `0`.
-/

open Finset

namespace MeanResidue

/-- The count `cnt n b` as a count of `k < n`. -/
theorem cnt_eq_card (n b : ℕ) (hn : 0 < n) (hb : b < n) :
    cnt n b = #{k ∈ range n | k ^ 2 % n = b} := by
  unfold cnt
  have : NeZero n := ⟨hn.ne'⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply card_bij (fun x _ => x.val)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_filter, mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    have h : ((x.val ^ 2 : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      simpa using hx
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb] at h
    exact h
  · intro x _ y _ h
    exact ZMod.val_injective n h
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    refine ⟨(k : ZMod n), ?_, ZMod.val_natCast_of_lt hk.1⟩
    simp only [mem_filter, mem_univ, true_and]
    have h : ((k ^ 2 : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff', hk.2, Nat.mod_eq_of_lt hb]
    push_cast at h
    simpa using h

/-- The number of `k < n` with `k² ≡ b (mod n)`, as a rational number. -/
def cR (n b : ℕ) : ℚ := (#{k ∈ range n | k ^ 2 % n = b} : ℚ)

/-- `n S n = ∑_{b<n} b #{k < n : k² ≡ b}`. -/
theorem S_mul (n : ℕ) (hn : 0 < n) :
    S n * n = ∑ b ∈ range n, (b : ℚ) * cR n b := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold S
  rw [div_mul_cancel₀ _ hnQ]
  have h := sum_fiberwise_of_maps_to' (s := range n) (t := range n) (g := fun k => k ^ 2 % n)
    (fun k _ => mem_range.2 (Nat.mod_lt _ hn)) (fun b => (b : ℚ))
  rw [← h]
  apply sum_congr rfl
  intro b _
  rw [sum_const, nsmul_eq_mul, mul_comm, cR]

/-- The counts add up to `n`. -/
theorem sum_card_fibers (n : ℕ) (hn : 0 < n) :
    ∑ b ∈ range n, cR n b = n := by
  have h := card_eq_sum_card_fiberwise (s := range n) (t := range n) (f := fun k => k ^ 2 % n)
    (fun k _ => mem_range.2 (Nat.mod_lt _ hn))
  rw [card_range] at h
  unfold cR
  exact_mod_cast h.symm

theorem s_eq_cR (n : ℕ) : (s n : ℚ) = cR n 0 := by
  simp only [s, cR, Nat.dvd_iff_mod_eq_zero]

theorem range_split (n : ℕ) (hn : 0 < n) (F : ℕ → ℚ) :
    ∑ b ∈ range n, F b = F 0 + ∑ b ∈ Ico 1 n, F b := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]

/-- Pairing `b` with `n - b` in a sum of Jacobi symbols `(b/d)` for `d ∣ n`. -/
theorem jac_reflect (n d : ℕ) (hd : d ∣ n) (hdo : Odd d) (g : ℕ → ℚ) (ε : ℚ)
    (hg : ∀ b ≤ n, g (n - b) = ε * g b) :
    ∑ b ∈ Ico 1 n, (jacobiSym b d : ℚ) * g b =
      ε * (ZMod.χ₄ d : ℚ) * ∑ b ∈ Ico 1 n, (jacobiSym b d : ℚ) * g b := by
  have h := sum_Ico_reflect (fun x => (jacobiSym x d : ℚ) * g x) 1 (show n ≤ n + 1 by omega)
  simp only [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega] at h
  calc ∑ b ∈ Ico 1 n, (jacobiSym b d : ℚ) * g b
      = ∑ b ∈ Ico 1 n, (jacobiSym ((n - b : ℕ) : ℤ) d : ℚ) * g (n - b) := h.symm
    _ = ∑ b ∈ Ico 1 n, ((ZMod.χ₄ d : ℚ) * jacobiSym b d) * (ε * g b) := by
        apply sum_congr rfl
        intro b hb
        rw [mem_Ico] at hb
        have hJ : jacobiSym ((n - b : ℕ) : ℤ) d = ZMod.χ₄ d * jacobiSym b d := by
          rw [← jacobiSym.neg _ hdo]
          apply jacobiSym.mod_left'
          obtain ⟨t, rfl⟩ := hd
          push_cast [Nat.cast_sub (show b ≤ d * t by omega)]
          rw [show (d : ℤ) * t - b = -b + d * t by ring, Int.add_mul_emod_self_left]
        rw [hJ, hg b (by omega)]
        push_cast
        ring
    _ = ε * (ZMod.χ₄ d : ℚ) * ∑ b ∈ Ico 1 n, (jacobiSym b d : ℚ) * g b := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        ring

/-- Summing `a (a/d)` over `t` periods. -/
theorem sum_block (d t : ℕ) (hP : ∑ b ∈ range d, (jacobiSym b d : ℚ) = 0) :
    ∑ a ∈ range (t * d), (a : ℚ) * jacobiSym a d = t * ∑ b ∈ range d, (b : ℚ) * jacobiSym b d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show (t + 1) * d = t * d + d by ring, sum_range_add, ih]
    have h : ∀ x ∈ range d, ((t * d + x : ℕ) : ℚ) * jacobiSym ((t * d + x : ℕ) : ℤ) d =
        (t * d : ℚ) * jacobiSym x d + (x : ℚ) * jacobiSym x d := by
      intro x _
      have hJ : jacobiSym ((t * d + x : ℕ) : ℤ) d = jacobiSym x d := by
        apply jacobiSym.mod_left'
        push_cast
        rw [show (t : ℤ) * d + x = x + d * t by ring, Int.add_mul_emod_self_left]
      rw [hJ]
      push_cast
      ring
    rw [sum_congr rfl h, sum_add_distrib, ← mul_sum, hP]
    push_cast
    ring

/-- `n · defect n = -∑_{0<b<n} c(b) (b - n/2)`. -/
theorem defect_mul (n : ℕ) (hn0 : 0 < n) :
    n * defect n = -∑ b ∈ Ico 1 n, cR n b * ((b : ℚ) - n / 2) := by
  have hS := S_mul n hn0
  have hT := sum_card_fibers n hn0
  rw [range_split n hn0] at hS hT
  simp only [Nat.cast_zero, zero_mul, zero_add] at hS
  unfold defect
  rw [s_eq_cR]
  have hT' : ∑ b ∈ Ico 1 n, cR n b = n - cR n 0 := by linarith
  calc (n : ℚ) * ((n - cR n 0) / 2 - S n)
      = (n / 2) * (∑ b ∈ Ico 1 n, cR n b) - S n * n := by rw [hT']; ring
    _ = (n / 2) * (∑ b ∈ Ico 1 n, cR n b) - ∑ b ∈ Ico 1 n, (b : ℚ) * cR n b := by rw [hS]
    _ = -∑ b ∈ Ico 1 n, cR n b * ((b : ℚ) - n / 2) := by
        rw [mul_sum, ← sum_sub_distrib, ← sum_neg_distrib]
        apply sum_congr rfl
        intro b _
        ring

/-- The contribution of one divisor `d`. -/
theorem divisor_term (n d : ℕ) (hd : d ∣ n) (hdo : Odd d) (hn0 : 0 < n) :
    ∑ b ∈ Ico 1 n, (jacobiSym b d : ℚ) * ((b : ℚ) - n / 2) =
      if d % 4 = 3 then -(n * hB d) else 0 := by
  have hodd_refl : ∀ b ≤ n, ((n - b : ℕ) : ℚ) - n / 2 = -1 * ((b : ℚ) - n / 2) := by
    intro b hb
    push_cast [Nat.cast_sub hb]
    ring
  have h1 := jac_reflect n d hd hdo (fun b => (b : ℚ) - n / 2) (-1) hodd_refl
  have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by
    rcases hdo with ⟨k, rfl⟩
    omega
  rcases hd4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h] at h1
    rw [ite_eq_right (by omega)]
    push_cast at h1
    linarith
  · rw [ite_eq_left h]
    have hχ : (ZMod.χ₄ d : ℚ) = -1 := by
      rw [ZMod.χ₄_nat_three_mod_four h]; norm_num
    -- the sum of `(b/d)` over `0 < b < m` vanishes for every multiple `m` of `d`
    have hzero : ∀ m, d ∣ m → ∑ b ∈ Ico 1 m, (jacobiSym b d : ℚ) = 0 := by
      intro m hm
      have := jac_reflect m d hm hdo (fun _ => (1 : ℚ)) 1 (fun _ _ => by ring)
      simp only [mul_one, one_mul, hχ] at this
      linarith
    have hd1 : 1 < d := by omega
    have hP : ∑ b ∈ range d, (jacobiSym b d : ℚ) = 0 := by
      rw [range_split d (by omega), hzero d dvd_rfl]
      simp [jacobiSym.zero_left hd1]
    obtain ⟨t, rfl⟩ := hd
    have hblock := sum_block d t hP
    rw [mul_comm t d] at hblock
    have e : ∑ b ∈ Ico 1 (d * t), (jacobiSym b d : ℚ) * ((b : ℚ) - ↑(d * t) / 2) =
        ∑ b ∈ Ico 1 (d * t), (b : ℚ) * jacobiSym b d -
          (↑(d * t) / 2) * ∑ b ∈ Ico 1 (d * t), (jacobiSym b d : ℚ) := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro b _
      ring
    rw [e, hzero (d * t) (dvd_mul_right d t), mul_zero, sub_zero]
    have e2 : ∑ b ∈ Ico 1 (d * t), (b : ℚ) * jacobiSym b d =
        ∑ a ∈ range (d * t), (a : ℚ) * jacobiSym a d := by
      rw [range_split _ hn0]
      simp
    rw [e2, hblock]
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    unfold hB
    push_cast
    field_simp

/-- **Theorem 1.1 at odd squarefree `n`, Bernoulli form**:
`(n - 1)/2 - S n = ∑_{d ∣ n, d ≡ 3 (mod 4)} hB d`. -/
theorem defect_squarefree {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    defect n = ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hcJ : ∀ b ∈ Ico 1 n, cR n b = ∑ d ∈ n.divisors, (jacobiSym b d : ℚ) := by
    intro b hb
    rw [mem_Ico] at hb
    have h := cnt_eq_sum_jacobi hn hodd b
    rw [cnt_eq_card n b hn0 hb.2] at h
    unfold cR
    exact_mod_cast h
  have key := defect_mul n hn0
  rw [sum_congr rfl (fun b hb => by rw [hcJ b hb]), ] at key
  simp only [sum_mul] at key
  rw [sum_comm] at key
  rw [sum_congr rfl (fun d hd => divisor_term n d (Nat.dvd_of_mem_divisors hd)
    (Odd.of_dvd_nat hodd (Nat.dvd_of_mem_divisors hd)) hn0)] at key
  rw [← sum_filter, sum_neg_distrib, neg_neg, ← mul_sum] at key
  exact mul_left_cancel₀ hnQ key

end MeanResidue
