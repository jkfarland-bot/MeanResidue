module

public import MeanResidue.EvenPeel

@[expose] public section

/-!
# Conjecture 7.5: the limits of `f(n)/n`, from a class number bound

Hypothesis (quoted from analytic number theory): `|G c| ≤ C √c (1 + log c)` for every `c ≥ 1`.
Since `G c = h*(-c) = (√c/π) L(1, -c)` for `c ≡ 0, 3 (mod 4)` and `G c = 0` otherwise, this is the
classical bound `|L(1, -c)| ≤ 3 + log c` (Section 5.3 of the note).

From it: `|defect n| ≤ C (1 + log n) ∑_{d ∣ n} √d`, and by Cauchy–Schwarz with `τ(n) ≤ 2√n` and
`σ(n) ≤ n (1 + log n)`, `(defect n / n)² ≤ 1458 C² n^(-1/8)`; also `s(n)² ≤ n`. With Theorem 1.2
(Lattice.lean) this gives `f(n)/n → 1/8, 0, -1/8, -1/4` along `n ≡ 0, 1, 2, 3 (mod 4)`.
-/

open Finset Filter Topology

namespace MeanResidue

/-! ### Divisor sums -/

/-- `τ(n) ≤ 2 √n`. -/
theorem card_divisors_le_two_sqrt (n : ℕ) : (#n.divisors : ℝ) ≤ 2 * Real.sqrt n := by
  set r := Nat.sqrt n
  set A := n.divisors.filter (fun d => d ≤ r)
  have hsub : n.divisors ⊆ A ∪ A.image (fun d => n / d) := by
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hn0 : n ≠ 0 := (Nat.mem_divisors.1 hd).2
    by_cases h : d ≤ r
    · exact mem_union_left _ (mem_filter.2 ⟨hd, h⟩)
    · apply mem_union_right
      rw [mem_image]
      refine ⟨n / d, mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd hdn, hn0⟩, ?_⟩,
        Nat.div_div_self hdn hn0⟩
      by_contra h'
      push Not at h h'
      have h1 : (r + 1) * (r + 1) ≤ (n / d) * d := Nat.mul_le_mul h' h
      rw [Nat.div_mul_cancel hdn] at h1
      have h2 : n < (r + 1) * (r + 1) := Nat.lt_succ_sqrt n
      exact absurd h1 (not_le.2 h2)
  have hA : #A ≤ r := by
    calc #A ≤ #(Icc 1 r) := card_le_card (fun d hd => by
            rw [mem_filter] at hd
            rw [mem_Icc]
            exact ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩)
      _ = r := by simp
  have h1 : #n.divisors ≤ 2 * r := by
    calc #n.divisors ≤ #(A ∪ A.image (fun d => n / d)) := card_le_card hsub
      _ ≤ #A + #(A.image (fun d => n / d)) := card_union_le _ _
      _ ≤ #A + #A := Nat.add_le_add_left card_image_le _
      _ ≤ 2 * r := by omega
  calc (#n.divisors : ℝ) ≤ 2 * r := by exact_mod_cast h1
    _ ≤ 2 * Real.sqrt n := by gcongr; exact Real.nat_sqrt_le_real_sqrt

/-- `σ(n) ≤ n (1 + log n)`. -/
theorem sum_divisors_le (n : ℕ) : ∑ d ∈ n.divisors, (d : ℝ) ≤ n * (1 + Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : ∑ d ∈ n.divisors, (d : ℝ) = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) :=
    (Nat.sum_div_divisors n (fun d => (d : ℝ))).symm
  have h2 : ∀ d ∈ n.divisors, ((n / d : ℕ) : ℝ) = n * (1 / d) := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
    ring
  rw [h1, sum_congr rfl h2, ← mul_sum]
  gcongr
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

/-- Cauchy–Schwarz: `(∑_{d ∣ n} √d)² ≤ τ(n) σ(n)`. -/
theorem sum_sqrt_divisors_sq (n : ℕ) :
    (∑ d ∈ n.divisors, Real.sqrt d) ^ 2 ≤ (#n.divisors : ℝ) * ∑ d ∈ n.divisors, (d : ℝ) := by
  have h := sum_mul_sq_le_sq_mul_sq n.divisors (fun _ => (1 : ℝ)) (fun d => Real.sqrt d)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
  have e : ∑ d ∈ n.divisors, Real.sqrt d ^ 2 = ∑ d ∈ n.divisors, (d : ℝ) := by
    apply sum_congr rfl
    intros
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [e] at h
  exact h

/-! ### `s(n)² ≤ n` -/

theorem s_mul_coprime {x y : ℕ} (h : Nat.Coprime x y) : s (x * y) = s x * s y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.coprime_zero_left] at h
    subst h
    simp [s]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [Nat.coprime_zero_right] at h
    subst h
    simp [s]
  rw [s_eq_cnt (Nat.mul_pos hx hy).ne', s_eq_cnt hx.ne', s_eq_cnt hy.ne', cnt_mul h]

theorem s_one : s 1 = 1 := by decide

theorem s_sq_dvd {n : ℕ} (hn : n ≠ 0) : s n ^ 2 ∣ n := by
  have hs : s n = n.factorization.prod fun p k => s (p ^ k) :=
    Nat.multiplicative_factorization s (fun x y h => s_mul_coprime h) s_one hn
  have hpp : ∀ p ∈ n.factorization.support, s (p ^ n.factorization p) = p ^ (n.factorization p / 2) := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    rw [s_eq_cnt (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero), cnt_prime_pow_zero]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [hs, Finsupp.prod, Finsupp.prod, ← prod_pow]
  apply prod_dvd_prod_of_dvd
  intro p hp
  rw [hpp p hp, ← pow_mul]
  exact pow_dvd_pow _ (by omega)

theorem s_sq_le (n : ℕ) : s n ^ 2 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s]
  exact Nat.le_of_dvd hn (s_sq_dvd hn.ne')

/-! ### The bound on `defect n` -/

theorem one_add_log_le {x : ℝ} (hx : 1 ≤ x) : 1 + Real.log x ≤ 9 * x ^ (1 / 8 : ℝ) := by
  have h1 : Real.log x ≤ x ^ (1 / 8 : ℝ) / (1 / 8) := Real.log_le_rpow_div (by linarith) (by norm_num)
  have h2 : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have h3 : x ^ (1 / 8 : ℝ) / (1 / 8) = 8 * x ^ (1 / 8 : ℝ) := by ring
  linarith

theorem defect_sq_bound {C : ℝ}
    (hC : ∀ c : ℕ, 0 < c → |(G c : ℝ)| ≤ C * Real.sqrt c * (1 + Real.log c)) {n : ℕ} (hn : 0 < n) :
    ((defect n : ℝ) / n) ^ 2 ≤ 1458 * C ^ 2 * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  set x : ℝ := (n : ℝ) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ C := by
    have := hC 1 one_pos
    simp only [Nat.cast_one, Real.sqrt_one, Real.log_one, add_zero, mul_one] at this
    exact le_trans (abs_nonneg _) this
  set L : ℝ := 1 + Real.log x with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    linarith
  -- `|defect n| ≤ C L ∑ √d`
  have hD : |(defect n : ℝ)| ≤ C * L * ∑ d ∈ n.divisors, Real.sqrt d := by
    rw [defect_eq_sum_G hn]
    push_cast
    calc |∑ d ∈ n.divisors, (G d : ℝ)| ≤ ∑ d ∈ n.divisors, |(G d : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ n.divisors, C * L * Real.sqrt d := by
          apply sum_le_sum
          intro d hd
          have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
          have hdn : (d : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast Nat.divisor_le hd
          have hlog : Real.log d ≤ Real.log x :=
            Real.log_le_log (by exact_mod_cast hd0) hdn
          calc |(G d : ℝ)| ≤ C * Real.sqrt d * (1 + Real.log d) := hC d hd0
            _ ≤ C * Real.sqrt d * L := by
                apply mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 (Real.sqrt_nonneg _))
            _ = C * L * Real.sqrt d := by ring
      _ = C * L * ∑ d ∈ n.divisors, Real.sqrt d := by rw [mul_sum]
  -- `(∑ √d)² ≤ 2 √x · x L`
  have hS : (∑ d ∈ n.divisors, Real.sqrt d) ^ 2 ≤ 2 * Real.sqrt x * (x * L) := by
    calc (∑ d ∈ n.divisors, Real.sqrt d) ^ 2 ≤ (#n.divisors : ℝ) * ∑ d ∈ n.divisors, (d : ℝ) :=
          sum_sqrt_divisors_sq n
      _ ≤ 2 * Real.sqrt x * (x * L) := by
          apply mul_le_mul (card_divisors_le_two_sqrt n) (sum_divisors_le n)
            (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
  have hS0 : 0 ≤ ∑ d ∈ n.divisors, Real.sqrt d := sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  -- `defect² ≤ 2 C² x √x L³`
  have hD2 : (defect n : ℝ) ^ 2 ≤ 2 * C ^ 2 * x * Real.sqrt x * L ^ 3 := by
    calc (defect n : ℝ) ^ 2 = |(defect n : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (C * L * ∑ d ∈ n.divisors, Real.sqrt d) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hD 2
      _ = C ^ 2 * L ^ 2 * (∑ d ∈ n.divisors, Real.sqrt d) ^ 2 := by ring
      _ ≤ C ^ 2 * L ^ 2 * (2 * Real.sqrt x * (x * L)) := by gcongr
      _ = 2 * C ^ 2 * x * Real.sqrt x * L ^ 3 := by ring
  -- `L³ ≤ 729 x^(3/8)`
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
  calc (defect n : ℝ) ^ 2 ≤ 2 * C ^ 2 * x * Real.sqrt x * L ^ 3 := hD2
    _ ≤ 2 * C ^ 2 * x * Real.sqrt x * (729 * x ^ (3 / 8 : ℝ)) := by gcongr
    _ = 1458 * C ^ 2 * (Real.sqrt x * x ^ (3 / 8 : ℝ) / x) * x ^ 2 := by
        field_simp
        ring

/-- Under the class number bound, `defect n = o(n)`. -/
theorem defect_div_tendsto {C : ℝ}
    (hC : ∀ c : ℕ, 0 < c → |(G c : ℝ)| ≤ C * Real.sqrt c * (1 + Real.log c)) :
    Tendsto (fun n : ℕ => (defect n : ℝ) / n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (1458 * C ^ 2 * (n : ℝ) ^ (-(1 / 8 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have h2 := (h1.const_mul (1458 * C ^ 2)).sqrt
    simpa using h2
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (defect_sq_bound hC hn)

theorem s_div_tendsto : Tendsto (fun n : ℕ => (s n : ℝ) / n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (1 / (n : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    simpa using h1.sqrt
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have hx0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, div_le_div_iff₀ (by positivity) hx0]
  have := s_sq_le n
  have h : ((s n : ℝ)) ^ 2 ≤ n := by exact_mod_cast this
  nlinarith

theorem comp_four_mul_add {u : ℕ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 L)) (r : ℕ) :
    Tendsto (fun k : ℕ => u (4 * k + r)) atTop (𝓝 L) :=
  hu.comp (tendsto_atTop_atTop.2 (fun b => ⟨b, fun k hk => by omega⟩))

/-- **Conjecture 7.5 of Chamberland and Dilcher**, from the class number bound
`|G c| ≤ C √c (1 + log c)`: `f(n)/n → 1/8, 0, -1/8, -1/4` along `n ≡ 0, 1, 2, 3 (mod 4)`. -/
theorem conj_7_5 {C : ℝ}
    (hC : ∀ c : ℕ, 0 < c → |(G c : ℝ)| ≤ C * Real.sqrt c * (1 + Real.log c)) :
    Tendsto (fun k : ℕ => (f (4 * k) : ℝ) / (4 * k : ℕ)) atTop (𝓝 (1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 1) : ℝ) / (4 * k + 1 : ℕ)) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 2) : ℝ) / (4 * k + 2 : ℕ)) atTop (𝓝 (-1 / 8)) ∧
    Tendsto (fun k : ℕ => (f (4 * k + 3) : ℝ) / (4 * k + 3 : ℕ)) atTop (𝓝 (-1 / 4)) := by
  have hD := defect_div_tendsto hC
  have hS := s_div_tendsto
  have hI : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  -- `f(n)/n = a + (s/n)/4 + b (1/n)/4 - (defect/n)/2` in each class
  have key : ∀ (a b : ℝ) (r : ℕ), (∀ n : ℕ, 0 < n → n % 4 = r % 4 →
      (f n : ℝ) / n = a + ((s n : ℝ) / n) / 4 + b * (1 / (n : ℝ)) / 4 - ((defect n : ℝ) / n) / 2) →
      Tendsto (fun k : ℕ => (f (4 * k + r) : ℝ) / (4 * k + r : ℕ)) atTop (𝓝 a) := by
    intro a b r h
    have hlim : Tendsto (fun n : ℕ => a + ((s n : ℝ) / n) / 4 + b * (1 / (n : ℝ)) / 4 -
        ((defect n : ℝ) / n) / 2) atTop (𝓝 a) := by
      have := ((tendsto_const_nhds (x := a)).add (hS.div_const 4)).add
        ((hI.const_mul b).div_const 4) |>.sub (hD.div_const 2)
      simpa using this
    have hcomp := comp_four_mul_add hlim r
    apply hcomp.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [h (4 * k + r) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key (1 / 8) 0 0 (fun n hn h4 => by
      rw [f_mod_four_eq_zero n hn (by omega)]
      have hx : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
      ring)
    simpa using this
  · exact key 0 (-1) 1 (fun n hn h4 => by
      rw [f_mod_four_eq_one n (by omega)]
      have hx : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
      ring)
  · exact key (-1 / 8) (-1) 2 (fun n hn h4 => by
      rw [f_mod_four_eq_two n (by omega)]
      have hx : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
      ring)
  · exact key (-1 / 4) 0 3 (fun n hn h4 => by
      rw [f_mod_four_eq_three n (by omega)]
      have hx : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
      ring)

end MeanResidue
