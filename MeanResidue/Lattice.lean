module

public import MeanResidue.Defs

@[expose] public section

/-!
# The floor sum `f n` through the mean residue `S n` (Theorem 1.2 relative to Theorem 1.1)

Counting the lattice points `(j, k)` with `1 ≤ j ≤ ⌊n/4⌋`, `k ≥ 1`, `k² ≤ jn` by rows, and pairing
`k` with `n - k`, gives `f n` in terms of `S n`, `s n` and `n mod 4`. With `defect n =
(n - s n)/2 - S n` the four cases read as in Theorem 1.2 of the paper.
-/

open Finset

namespace MeanResidue

/-- `⌊√m⌋` counts the `k ∈ [1, B]` with `k² ≤ m`, once `B ≥ ⌊√m⌋`. -/
theorem sqrt_eq_card (m B : ℕ) (h : Nat.sqrt m ≤ B) :
    Nat.sqrt m = #{k ∈ Icc 1 B | k ^ 2 ≤ m} := by
  have : ({k ∈ Icc 1 B | k ^ 2 ≤ m} : Finset ℕ) = Icc 1 (Nat.sqrt m) := by
    ext k
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, Nat.le_sqrt'.2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans h⟩, Nat.le_sqrt'.1 h2⟩
  rw [this, Nat.card_Icc]
  omega

/-- For `k ≥ 1`, the `j ∈ [1, J]` with `k² ≤ jn` are those with `j > ⌊(k² - 1)/n⌋`. -/
theorem card_j (n J k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkJ : (k ^ 2 - 1) / n ≤ J) :
    #{j ∈ Icc 1 J | k ^ 2 ≤ j * n} = J - (k ^ 2 - 1) / n := by
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have : ({j ∈ Icc 1 J | k ^ 2 ≤ j * n} : Finset ℕ) = Icc ((k ^ 2 - 1) / n + 1) J := by
    ext j
    simp only [mem_filter, mem_Icc]
    have key : k ^ 2 ≤ j * n ↔ (k ^ 2 - 1) / n < j := by
      constructor
      · intro h
        exact (Nat.div_lt_iff_lt_mul hn).2 (by omega)
      · intro h
        have := (Nat.div_lt_iff_lt_mul hn).1 h
        omega
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨key.1 h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨le_trans (Nat.le_add_left 1 _) h1, h2⟩, key.2 h1⟩
  rw [this, Nat.card_Icc]
  omega

/-- Counting by rows: `∑_{j ≤ J} ⌊√(jn)⌋ = ∑_{k ≤ 2J} (J - ⌊(k² - 1)/n⌋)` for `J = ⌊n/4⌋`. -/
theorem sum_sqrt_eq (n J : ℕ) (hn : 0 < n) (hJ : 4 * J ≤ n) (hJ' : n < 4 * J + 4) :
    ∑ j ∈ Icc 1 J, Nat.sqrt (j * n) = ∑ k ∈ Icc 1 (2 * J), (J - (k ^ 2 - 1) / n) := by
  have h1 : ∀ j ∈ Icc 1 J, Nat.sqrt (j * n) = #{k ∈ Icc 1 (2 * J) | k ^ 2 ≤ j * n} := by
    intro j hj
    apply sqrt_eq_card
    rw [mem_Icc] at hj
    have h2 : j * n ≤ J * (4 * J + 3) := Nat.mul_le_mul hj.2 (by omega)
    have h3 : j * n < (2 * J + 1) ^ 2 := by nlinarith
    exact Nat.lt_succ_iff.1 (Nat.sqrt_lt'.2 h3)
  rw [sum_congr rfl h1]
  simp only [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [mem_Icc] at hk
  rw [← card_filter]
  apply card_j n J k hn hk.1
  have h3 : k ^ 2 ≤ (2 * J) ^ 2 := Nat.pow_le_pow_left hk.2 2
  have h4 : (J + 1) * (4 * J) ≤ (J + 1) * n := Nat.mul_le_mul_left _ hJ
  have h5 : 1 ≤ J := by omega
  have h6 : k ^ 2 < (J + 1) * n := by nlinarith
  have h7 : (k ^ 2 - 1) / n < J + 1 := (Nat.div_lt_iff_lt_mul hn).2 (by omega)
  omega

/-- `⌊(k² - 1)/n⌋ + [n ∣ k²] = ⌊k²/n⌋` for `k ≥ 1`. -/
theorem div_pred_add (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    (k ^ 2 - 1) / n + (if n ∣ k ^ 2 then 1 else 0) = k ^ 2 / n := by
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hdm := Nat.div_add_mod' (k ^ 2) n
  have hrn : k ^ 2 % n < n := Nat.mod_lt _ hn
  split_ifs with hdvd
  · have hr0 : k ^ 2 % n = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hq1 : 1 ≤ k ^ 2 / n := by
      rcases Nat.eq_zero_or_pos (k ^ 2 / n) with h | h
      · rw [h, hr0] at hdm; omega
      · exact h
    obtain ⟨q, hq⟩ : ∃ q, k ^ 2 / n = q + 1 := ⟨k ^ 2 / n - 1, by omega⟩
    rw [hq] at hdm ⊢
    have e1 : (q + 1) * n = q * n + n := by ring
    rw [hr0, e1] at hdm
    have : (k ^ 2 - 1) / n = q := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [e1]; omega
    omega
  · have hr1 : 1 ≤ k ^ 2 % n := by
      rcases Nat.eq_zero_or_pos (k ^ 2 % n) with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hdvd
      · exact h
    have : (k ^ 2 - 1) / n = k ^ 2 / n := by
      apply Nat.div_eq_of_lt_le
      · omega
      · have e1 : (k ^ 2 / n + 1) * n = k ^ 2 / n * n + n := by ring
        rw [e1]; omega
    omega

/-- `⌊(k² - 1)/n⌋ = (k² - Rem(k² ÷ n))/n - [n ∣ k²]` for `k ≥ 1`, in `ℚ`. -/
theorem cast_div_pred (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    (((k ^ 2 - 1) / n : ℕ) : ℚ) =
      ((k : ℚ) ^ 2 - ((k ^ 2 % n : ℕ) : ℚ)) / n - (if n ∣ k ^ 2 then 1 else 0) := by
  have h1 := div_pred_add n k hn hk
  have hdm := Nat.div_add_mod' (k ^ 2) n
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (((k ^ 2 - 1) / n : ℕ) : ℚ) + (if n ∣ k ^ 2 then (1 : ℚ) else 0) =
      ((k ^ 2 / n : ℕ) : ℚ) := by
    rw [← h1]; push_cast; split_ifs <;> simp
  have h3 : ((k ^ 2 / n : ℕ) : ℚ) * n + ((k ^ 2 % n : ℕ) : ℚ) = (k : ℚ) ^ 2 := by
    exact_mod_cast hdm
  have h4 : ((k ^ 2 / n : ℕ) : ℚ) = ((k : ℚ) ^ 2 - ((k ^ 2 % n : ℕ) : ℚ)) / n := by
    field_simp; linarith
  linarith

/-- Pairing `k` with `n - k` for a function symmetric under `k ↦ n - k`. -/
theorem reflect_sum (n m : ℕ) (hm : m < n) (F : ℕ → ℚ) (hF : ∀ k ≤ n, F (n - k) = F k) :
    2 * ∑ k ∈ Icc 1 m, F k =
      ∑ k ∈ Ico 1 n, F k * ((if k ∈ Icc 1 m then 1 else 0) +
        (if n - k ∈ Icc 1 m then 1 else 0)) := by
  have hsub : Icc 1 m ⊆ Ico 1 n := by
    intro k
    simp only [mem_Icc, mem_Ico]
    omega
  have A : ∑ k ∈ Ico 1 n, F k * (if k ∈ Icc 1 m then (1 : ℚ) else 0) = ∑ k ∈ Icc 1 m, F k := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, inter_eq_right.2 hsub]
  have B : ∑ k ∈ Ico 1 n, F k * (if n - k ∈ Icc 1 m then (1 : ℚ) else 0) =
      ∑ k ∈ Ico 1 n, F k * (if k ∈ Icc 1 m then (1 : ℚ) else 0) := by
    have := sum_Ico_reflect (fun x => F x * (if n - x ∈ Icc 1 m then (1 : ℚ) else 0)) 1
      (show n ≤ n + 1 by omega)
    simp only [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega] at this
    rw [← this]
    apply sum_congr rfl
    intro k hk
    rw [mem_Ico] at hk
    rw [hF k (by omega), show n - (n - k) = k by omega]
  simp only [mul_add, sum_add_distrib]
  rw [B, A]
  ring

/-- The summand `Rem(k² ÷ n)/n + [n ∣ k²]`. -/
def F (n k : ℕ) : ℚ := ((k ^ 2 % n : ℕ) : ℚ) / n + (if n ∣ k ^ 2 then 1 else 0)

theorem sq_mod_reflect (n k : ℕ) (hk : k ≤ n) : (n - k) ^ 2 % n = k ^ 2 % n := by
  have : (((n - k) ^ 2 : ℕ) : ZMod n) = ((k ^ 2 : ℕ) : ZMod n) := by
    push_cast [Nat.cast_sub hk, ZMod.natCast_self]
    ring
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 this

theorem F_reflect (n k : ℕ) (hk : k ≤ n) : F n (n - k) = F n k := by
  have hmod := sq_mod_reflect n k hk
  have hd : n ∣ (n - k) ^ 2 ↔ n ∣ k ^ 2 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hmod]
  unfold F
  rw [hmod]
  by_cases h : n ∣ k ^ 2
  · simp [h, hd.2 h]
  · simp [h, show ¬ n ∣ (n - k) ^ 2 from fun h' => h (hd.1 h')]

/-- For `k ≤ 2J`, `⌊(k² - 1)/n⌋ ≤ J`. -/
theorem div_pred_le (n J k : ℕ) (hn : 0 < n) (hJ : 4 * J ≤ n) (hk : k ≤ 2 * J) :
    (k ^ 2 - 1) / n ≤ J := by
  rcases Nat.eq_zero_or_pos J with h0 | h5
  · subst h0
    have : k = 0 := by omega
    subst this; simp
  have h3 : k ^ 2 ≤ (2 * J) ^ 2 := Nat.pow_le_pow_left hk 2
  have h4 : (J + 1) * (4 * J) ≤ (J + 1) * n := Nat.mul_le_mul_left _ hJ
  have h6 : k ^ 2 < (J + 1) * n := by nlinarith
  have h7 : (k ^ 2 - 1) / n < J + 1 := (Nat.div_lt_iff_lt_mul hn).2 (by omega)
  omega

/-- `∑_{k ≤ m} k² = m(m+1)(2m+1)/6`. -/
theorem sum_sq_Icc (m : ℕ) : ∑ k ∈ Icc 1 m, ((k : ℚ) ^ 2) = m * (m + 1) * (2 * m + 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The floor sum as `2J² - (1/n) ∑_{k ≤ 2J} k² + ∑_{k ≤ 2J} F n k - (n² - 1)/12`. -/
theorem f_eq_main (n : ℕ) (hn : 0 < n) :
    f n = 2 * ((n / 4 : ℕ) : ℚ) * (n / 4 : ℕ) -
      (∑ k ∈ Icc 1 (2 * (n / 4)), ((k : ℚ) ^ 2)) / n + ∑ k ∈ Icc 1 (2 * (n / 4)), F n k -
      ((n : ℚ) ^ 2 - 1) / 12 := by
  set J := n / 4 with hJdef
  have hJ : 4 * J ≤ n := by omega
  have hJ' : n < 4 * J + 4 := by omega
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold f
  rw [← hJdef]
  have h1 : (∑ j ∈ Icc 1 J, (Nat.sqrt (j * n) : ℚ)) =
      ((∑ k ∈ Icc 1 (2 * J), (J - (k ^ 2 - 1) / n) : ℕ) : ℚ) := by
    rw [← sum_sqrt_eq n J hn hJ hJ']
    push_cast
    rfl
  rw [h1]
  push_cast
  have h2 : ∀ k ∈ Icc 1 (2 * J), (((J - (k ^ 2 - 1) / n : ℕ)) : ℚ) =
      (J : ℚ) - (k : ℚ) ^ 2 / n + F n k := by
    intro k hk
    rw [mem_Icc] at hk
    rw [Nat.cast_sub (div_pred_le n J k hn hJ hk.2), cast_div_pred n k hn hk.1]
    unfold F
    field_simp
    ring
  rw [sum_congr rfl h2]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
  rw [← sum_div]
  push_cast
  ring

/-- `∑_{k<n} F n k = S n + s n`. -/
theorem sum_F_range (n : ℕ) : ∑ k ∈ range n, F n k = S n + s n := by
  unfold F S s
  rw [sum_add_distrib, ← sum_div, sum_boole]

/-- `∑_{0<k<n} F n k = S n + s n - 1`. -/
theorem sum_F_Ico (n : ℕ) (hn : 0 < n) : ∑ k ∈ Ico 1 n, F n k = S n + s n - 1 := by
  have h := sum_F_range n
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn] at h
  have h0 : F n 0 = 1 := by unfold F; simp
  rw [h0] at h
  linarith

/-- The reflected weights, as a sum. -/
theorem sum_weights (n m : ℕ) (hm : m < n) (c : ℕ → ℚ)
    (hc : ∀ k ∈ Ico 1 n, ((if k ∈ Icc 1 m then (1 : ℚ) else 0) +
      (if n - k ∈ Icc 1 m then 1 else 0)) = 1 + c k) :
    2 * ∑ k ∈ Icc 1 m, F n k = (S n + s n - 1) + ∑ k ∈ Ico 1 n, F n k * c k := by
  rw [reflect_sum n m hm (F n) (fun k hk => F_reflect n k hk), sum_congr rfl
    (fun k hk => by rw [hc k hk]), ← sum_F_Ico n (by omega), ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  ring

theorem F_mid3a (J : ℕ) : F (4 * J + 3) (2 * J + 1) = (J + 1) / (4 * J + 3) := by
  have hm : (2 * J + 1) ^ 2 % (4 * J + 3) = J + 1 := by
    rw [show (2 * J + 1) ^ 2 = (J + 1) + (4 * J + 3) * J by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hd : ¬ (4 * J + 3) ∣ (2 * J + 1) ^ 2 := by
    rw [Nat.dvd_iff_mod_eq_zero, hm]; omega
  unfold F
  rw [hm, ite_eq_right hd]
  push_cast
  ring

theorem F_mid3b (J : ℕ) : F (4 * J + 3) (2 * J + 2) = (J + 1) / (4 * J + 3) := by
  have hm : (2 * J + 2) ^ 2 % (4 * J + 3) = J + 1 := by
    rw [show (2 * J + 2) ^ 2 = (J + 1) + (4 * J + 3) * (J + 1) by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hd : ¬ (4 * J + 3) ∣ (2 * J + 2) ^ 2 := by
    rw [Nat.dvd_iff_mod_eq_zero, hm]; omega
  unfold F
  rw [hm, ite_eq_right hd]
  push_cast
  ring

theorem F_mid0 (J : ℕ) : F (4 * J) (2 * J) = 1 := by
  have hm : (2 * J) ^ 2 % (4 * J) = 0 := by
    rw [show (2 * J) ^ 2 = (4 * J) * J by ring, Nat.mul_mod_right]
  unfold F
  rw [hm, ite_eq_left (Nat.dvd_of_mod_eq_zero hm)]
  simp

theorem F_mid2 (J : ℕ) : F (4 * J + 2) (2 * J + 1) = 1 / 2 := by
  have hm : (2 * J + 1) ^ 2 % (4 * J + 2) = 2 * J + 1 := by
    rw [show (2 * J + 1) ^ 2 = (2 * J + 1) + (4 * J + 2) * J by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hd : ¬ (4 * J + 2) ∣ (2 * J + 1) ^ 2 := by
    rw [Nat.dvd_iff_mod_eq_zero, hm]; omega
  unfold F
  rw [hm, ite_eq_right hd]
  push_cast
  field_simp
  ring

/-- **Theorem 1.2, case `n ≡ 1 (mod 4)`**: `f n = (s n - 1)/4 - defect n / 2`. -/
theorem f_mod_four_eq_one (n : ℕ) (h : n % 4 = 1) : f n = ((s n : ℚ) - 1) / 4 - defect n / 2 := by
  obtain ⟨J, rfl⟩ : ∃ J, n = 4 * J + 1 := ⟨n / 4, by omega⟩
  have hJ : (4 * J + 1) / 4 = J := by omega
  have hw := sum_weights (4 * J + 1) (2 * J) (by omega) (fun _ => 0) (by
    intro k hk
    rw [mem_Ico] at hk
    simp only [mem_Icc]
    split_ifs <;> (try norm_num) <;> omega)
  simp only [mul_zero, sum_const_zero, add_zero] at hw
  have hsum : ∑ k ∈ Icc 1 (2 * J), F (4 * J + 1) k = (S (4 * J + 1) + s (4 * J + 1) - 1) / 2 := by
    linarith
  rw [f_eq_main _ (by omega), hJ, sum_sq_Icc, hsum]
  unfold defect
  push_cast
  field_simp
  ring

/-- **Theorem 1.2, case `n ≡ 3 (mod 4)`**: `f n = (s n - n)/4 - defect n / 2`. -/
theorem f_mod_four_eq_three (n : ℕ) (h : n % 4 = 3) :
    f n = ((s n : ℚ) - n) / 4 - defect n / 2 := by
  obtain ⟨J, rfl⟩ : ∃ J, n = 4 * J + 3 := ⟨n / 4, by omega⟩
  have hJ : (4 * J + 3) / 4 = J := by omega
  have hw := sum_weights (4 * J + 3) (2 * J) (by omega)
    (fun k => -(if k = 2 * J + 1 then 1 else 0) - (if k = 2 * J + 2 then 1 else 0)) (by
    intro k hk
    rw [mem_Ico] at hk
    simp only [mem_Icc]
    split_ifs <;> (try norm_num) <;> omega)
  have e : ∑ k ∈ Ico 1 (4 * J + 3), F (4 * J + 3) k *
      (-(if k = 2 * J + 1 then (1 : ℚ) else 0) - (if k = 2 * J + 2 then 1 else 0)) =
      -F (4 * J + 3) (2 * J + 1) - F (4 * J + 3) (2 * J + 2) := by
    simp only [mul_sub, mul_neg, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_neg_distrib,
      sum_ite_eq', mem_Ico]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  rw [e, F_mid3a, F_mid3b] at hw
  have hsum : ∑ k ∈ Icc 1 (2 * J), F (4 * J + 3) k = (S (4 * J + 3) + s (4 * J + 3) - 1 -
      2 * ((J + 1) / (4 * J + 3))) / 2 := by
    linarith
  rw [f_eq_main _ (by omega), hJ, sum_sq_Icc, hsum]
  unfold defect
  push_cast
  field_simp
  ring

/-- **Theorem 1.2, case `n ≡ 0 (mod 4)`**: `f n = n/8 + s n / 4 - defect n / 2`. -/
theorem f_mod_four_eq_zero (n : ℕ) (hn : 0 < n) (h : n % 4 = 0) :
    f n = (n : ℚ) / 8 + (s n : ℚ) / 4 - defect n / 2 := by
  obtain ⟨J, rfl⟩ : ∃ J, n = 4 * J := ⟨n / 4, by omega⟩
  have hJ1 : 1 ≤ J := by omega
  have hJ : 4 * J / 4 = J := by omega
  have hw := sum_weights (4 * J) (2 * J) (by omega)
    (fun k => if k = 2 * J then 1 else 0) (by
    intro k hk
    rw [mem_Ico] at hk
    simp only [mem_Icc]
    split_ifs <;> (try norm_num) <;> omega)
  have e : ∑ k ∈ Ico 1 (4 * J), F (4 * J) k * (if k = 2 * J then (1 : ℚ) else 0) =
      F (4 * J) (2 * J) := by
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_Ico]
    rw [ite_eq_left (by omega)]
  rw [e, F_mid0 J] at hw
  have hsum : ∑ k ∈ Icc 1 (2 * J), F (4 * J) k = (S (4 * J) + s (4 * J)) / 2 := by
    linarith
  have hJQ : (J : ℚ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
  rw [f_eq_main _ hn, hJ, sum_sq_Icc, hsum]
  unfold defect
  push_cast
  field_simp
  ring

/-- **Theorem 1.2, case `n ≡ 2 (mod 4)`**: `f n = -n/8 + (s n - 1)/4 - defect n / 2`. -/
theorem f_mod_four_eq_two (n : ℕ) (h : n % 4 = 2) :
    f n = -(n : ℚ) / 8 + ((s n : ℚ) - 1) / 4 - defect n / 2 := by
  obtain ⟨J, rfl⟩ : ∃ J, n = 4 * J + 2 := ⟨n / 4, by omega⟩
  have hJ : (4 * J + 2) / 4 = J := by omega
  have hw := sum_weights (4 * J + 2) (2 * J) (by omega)
    (fun k => -(if k = 2 * J + 1 then 1 else 0)) (by
    intro k hk
    rw [mem_Ico] at hk
    simp only [mem_Icc]
    split_ifs <;> (try norm_num) <;> omega)
  have e : ∑ k ∈ Ico 1 (4 * J + 2), F (4 * J + 2) k * (-(if k = 2 * J + 1 then (1 : ℚ) else 0)) =
      -F (4 * J + 2) (2 * J + 1) := by
    simp only [mul_neg, mul_ite, mul_one, mul_zero, sum_neg_distrib, sum_ite_eq', mem_Ico]
    rw [ite_eq_left (by omega)]
  rw [e, F_mid2] at hw
  have hsum : ∑ k ∈ Icc 1 (2 * J), F (4 * J + 2) k =
      (S (4 * J + 2) + s (4 * J + 2) - 1 - 1 / 2) / 2 := by
    linarith
  rw [f_eq_main _ (by omega), hJ, sum_sq_Icc, hsum]
  unfold defect
  push_cast
  field_simp
  ring

end MeanResidue
