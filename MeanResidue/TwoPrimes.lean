module

public import MeanResidue.OddPeel

@[expose] public section

/-!
# Two prime factors: Conjectures 7.1 and 7.2 of Chamberland and Dilcher

For distinct odd primes `p, q` and `n = p^α q^β`:
* (7.1, with the sign of the `h*(-pq)` term corrected) if `p ≡ 1`, `q ≡ 3 (mod 4)`:
  `S_n = (n - s(n))/2 - [⌊(β+1)/2⌋]_q (([⌊α/2⌋+1]_p - (p/q)[⌊α/2⌋]_p) h*(-q) + [⌊(α+1)/2⌋]_p h*(-pq))`;
* (7.2) if `p ≡ q ≡ 3 (mod 4)`:
  `S_n = (n - s(n))/2 - ((p/q)[⌊β/2⌋]_q + [⌊β/2⌋+1]_q)[⌊(α+1)/2⌋]_p h*(-p)
          - ((q/p)[⌊α/2⌋]_p + [⌊α/2⌋+1]_p)[⌊(β+1)/2⌋]_q h*(-q)`,
with `[e]_ℓ = 1 + ℓ + ⋯ + ℓ^(e-1)` (`geom ℓ e`), `s(n) = p^⌊α/2⌋ q^⌊β/2⌋`, and `h*(-d)` in Bernoulli form
`hB d` (Dirichlet's class number formula, quoted).
-/

open Finset

namespace MeanResidue

/-- `[e]_ℓ = 1 + ℓ + ⋯ + ℓ^(e-1)`. -/
def geom (ℓ e : ℕ) : ℚ := ∑ i ∈ range e, (ℓ : ℚ) ^ i

/-! ### `s` -/

theorem s_eq_cnt {n : ℕ} (hn : n ≠ 0) : s n = cnt n 0 := by
  rw [cnt_eq_card_range hn, s]
  congr 1
  apply filter_congr
  intro x _
  rw [sub_zero]
  norm_cast

theorem cnt_prime_pow_zero (p : ℕ) [Fact p.Prime] (e : ℕ) : cnt (p ^ e) 0 = p ^ (e / 2) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  match e with
  | 0 => simp [cnt_one]
  | 1 =>
    rw [pow_one, cnt_prime_of_dvd p (dvd_zero _)]
    simp
  | e + 2 =>
    have h := cnt_pow_add_two_mul_sq p e 0
    rw [mul_zero] at h
    rw [h, ih e (by omega), show (e + 2) / 2 = e / 2 + 1 by omega, pow_succ]
    ring

/-- `s(p^α q^β) = p^⌊α/2⌋ q^⌊β/2⌋`. -/
theorem s_pow_mul_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (α β : ℕ) :
    s (p ^ α * q ^ β) = p ^ (α / 2) * q ^ (β / 2) := by
  have hp' := Fact.mk hp
  have hq' := Fact.mk hq
  rw [s_eq_cnt (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne',
    cnt_mul (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq)), cnt_prime_pow_zero,
    cnt_prime_pow_zero]

/-! ### Bookkeeping -/

theorem sum_divisors_pow_mul_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (α β : ℕ)
    (F : ℕ → ℚ) :
    ∑ d ∈ (p ^ α * q ^ β).divisors, F d =
      ∑ a ∈ range (α + 1), ∑ b ∈ range (β + 1), F (p ^ a * q ^ b) := by
  have hcop : Nat.Coprime (p ^ α) (q ^ β) := Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq)
  rw [Nat.divisors_mul, Finset.mul_def,
    sum_image (fun x hx y hy h => hcop.mul_injOn_divisors (by exact_mod_cast hx) (by exact_mod_cast hy) h),
    sum_product, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro a _
  rw [Nat.sum_divisors_prime_pow hq]

theorem sum_range_parity (F : ℕ → ℚ) (N : ℕ) :
    ∑ a ∈ range (N + 1), F a =
      ∑ i ∈ range (N / 2 + 1), F (2 * i) + ∑ i ∈ range ((N + 1) / 2), F (2 * i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
    · have e1 : 2 * k / 2 = k := by omega
      have e2 : (2 * k + 1) / 2 = k := by omega
      have e3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [e1, e2, e3, sum_range_succ (fun i => F (2 * i + 1)) k]
      ring
    · have e1 : (2 * k + 1) / 2 = k := by omega
      have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have e3 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
      rw [e1, e2, e3, sum_range_succ (fun i => F (2 * i)) (k + 1),
        show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      ring

theorem sum_tower (ℓ : ℕ) (J : ℚ) (k : ℕ) :
    ∑ i ∈ range (k + 1), (if i = 0 then (1 : ℚ) else (ℓ : ℚ) ^ (i - 1) * (ℓ - J)) =
      geom ℓ (k + 1) - J * geom ℓ k := by
  have h1 : ∀ i ∈ range k, (if i + 1 = 0 then (1 : ℚ) else (ℓ : ℚ) ^ (i + 1 - 1) * (ℓ - J)) =
      (ℓ : ℚ) ^ (i + 1) - J * (ℓ : ℚ) ^ i := by
    intro i _
    rw [ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    ring
  rw [sum_range_succ', sum_congr rfl h1, sum_sub_distrib, ← mul_sum, geom, geom,
    sum_range_succ' (fun i => (ℓ : ℚ) ^ i), ite_eq_left rfl, pow_zero]
  ring

theorem pow_mod_four_three {q : ℕ} (hq : q % 4 = 3) (b : ℕ) :
    q ^ b % 4 = if b % 2 = 1 then 3 else 1 := by
  rw [Nat.pow_mod, hq]
  rcases Nat.even_or_odd' b with ⟨k, rfl | rfl⟩
  · rw [ite_eq_right (by omega), pow_mul, Nat.pow_mod]
    norm_num
  · rw [ite_eq_left (by omega), pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem pow_mod_four_one {p : ℕ} (hp : p % 4 = 1) (a : ℕ) : p ^ a % 4 = 1 := by
  rw [Nat.pow_mod, hp, one_pow, Nat.one_mod]

theorem sq_pow_mod_four {ℓ : ℕ} (hℓ : ℓ % 2 = 1) (i : ℕ) : ℓ ^ (2 * i) % 4 = 1 := by
  have h2 : ℓ ^ 2 % 4 = 1 := by
    have h : ℓ % 4 = 1 ∨ ℓ % 4 = 3 := by omega
    rcases h with h | h <;> rw [Nat.pow_mod, h]
  rw [pow_mul, Nat.pow_mod, h2, one_pow, Nat.one_mod]

/-! ### Towers -/

/-- `G (ℓ^(2i) c) = ℓ^i G c` when the prime `ℓ` divides `c ≡ 3 (mod 4)`. -/
theorem G_pow_dvd {ℓ c : ℕ} (hℓ : ℓ.Prime) (hc : c % 4 = 3) (hdvd : ℓ ∣ c) (i : ℕ) :
    G (ℓ ^ (2 * i) * c) = ℓ ^ i * G c := by
  have hℓo : ℓ % 2 = 1 := Nat.odd_iff.1 (Odd.of_dvd_nat (Nat.odd_iff.2 (by omega)) hdvd)
  induction i with
  | zero => simp
  | succ i ih =>
    have hc' : ℓ ^ (2 * i) * c % 4 = 3 := by rw [Nat.mul_mod, sq_pow_mod_four hℓo i, hc]
    have hne : ℓ ^ (2 * i) * c ≠ 0 := (Nat.mul_pos (pow_pos hℓ.pos _) (by omega)).ne'
    rw [show ℓ ^ (2 * (i + 1)) * c = ℓ ^ 2 * (ℓ ^ (2 * i) * c) by ring, G_peel hℓ hc', ih,
      jacobiSym_eq_zero_of_dvd hℓ hne (dvd_mul_of_dvd_right hdvd _)]
    push_cast
    ring

/-- `G (ℓ^(2i+2) c) = ℓ^i (ℓ - (ℓ/c)) G c` for an odd prime `ℓ ∤ c`, `c ≡ 3 (mod 4)`. -/
theorem G_pow_coprime {ℓ c : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hc : c % 4 = 3) (i : ℕ) :
    G (ℓ ^ (2 * i + 2) * c) = ℓ ^ i * (ℓ - jacobiSym ℓ c) * G c := by
  have hℓo : ℓ % 2 = 1 := Nat.odd_iff.1 (hℓ.odd_of_ne_two hℓ2)
  have hc2 : ℓ ^ 2 * c % 4 = 3 := by
    rw [Nat.mul_mod, show ℓ ^ 2 = ℓ ^ (2 * 1) by ring, sq_pow_mod_four hℓo 1, hc]
  rw [show ℓ ^ (2 * i + 2) * c = ℓ ^ (2 * i) * (ℓ ^ 2 * c) by ring,
    G_pow_dvd hℓ hc2 (dvd_mul_of_dvd_left (dvd_pow_self ℓ two_ne_zero) c) i, G_peel hℓ hc]
  ring

/-- `G (r^(2j+1)) = r^j hB r` for a prime `r ≡ 3 (mod 4)`. -/
theorem G_prime_tower {r : ℕ} (hr : r.Prime) (hr4 : r % 4 = 3) (j : ℕ) :
    G (r ^ (2 * j + 1)) = r ^ j * hB r := by
  rw [show r ^ (2 * j + 1) = r ^ (2 * j) * r by ring, G_pow_dvd hr hr4 dvd_rfl j,
    G_squarefree hr.squarefree hr4]

theorem jacobiSym_odd_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    jacobiSym p (q ^ (2 * j + 1)) = jacobiSym p q := by
  have hJ : jacobiSym p q ^ 2 = 1 := by
    apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hp hq).2 hpq
  rw [jacobiSym.pow_right, pow_succ, pow_mul, hJ, one_pow, one_mul]

/-- `G (p^(2i) q^(2j+1))` for an odd prime `p ≠ q` and a prime `q ≡ 3 (mod 4)`. -/
theorem G_even_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2)
    (hq4 : q % 4 = 3) (i j : ℕ) :
    G (p ^ (2 * i) * q ^ (2 * j + 1)) =
      (if i = 0 then (1 : ℚ) else (p : ℚ) ^ (i - 1) * (p - jacobiSym p q)) * (q ^ j * hB q) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [G_prime_tower hq hq4]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hc : q ^ (2 * j + 1) % 4 = 3 := by rw [pow_mod_four_three hq4, ite_eq_left (by omega)]
    rw [show 2 * (i' + 1) = 2 * i' + 2 by ring, G_pow_coprime hp hp2 hc,
      jacobiSym_odd_pow hp hq hpq, G_prime_tower hq hq4, ite_eq_right (by omega),
      Nat.add_sub_cancel]

/-- `G (p^(2i+1) q^(2j+1)) = p^i q^j hB(pq)` for distinct odd primes with `pq ≡ 3 (mod 4)`. -/
theorem G_odd_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h4 : p * q % 4 = 3) (i j : ℕ) :
    G (p ^ (2 * i + 1) * q ^ (2 * j + 1)) = p ^ i * q ^ j * hB (p * q) := by
  have hqo : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · subst h
      omega
    · exact h
  have hsq : Squarefree (p * q) :=
    Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_primes hp hq).2 hpq, hp.squarefree, hq.squarefree⟩
  have hc : q ^ (2 * j) * (p * q) % 4 = 3 := by rw [Nat.mul_mod, sq_pow_mod_four hqo j, h4]
  rw [show p ^ (2 * i + 1) * q ^ (2 * j + 1) = p ^ (2 * i) * (q ^ (2 * j) * (p * q)) by ring,
    G_pow_dvd hp hc (dvd_mul_of_dvd_right (dvd_mul_right p q) _) i,
    G_pow_dvd hq h4 (dvd_mul_left q p) j, G_squarefree hsq h4]
  ring

theorem S_eq_sub_defect (n : ℕ) : S n = ((n : ℚ) - s n) / 2 - defect n := by
  unfold defect
  ring

theorem divisor_sum_pow_mul_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (α β : ℕ) :
    defect (p ^ α * q ^ β) = ∑ a ∈ range (α + 1), ∑ b ∈ range (β + 1),
      (if p ^ a * q ^ b % 4 = 3 then G (p ^ a * q ^ b) else 0) := by
  have hn : Odd (p ^ α * q ^ β) :=
    Odd.mul ((hp.odd_of_ne_two hp2).pow) ((hq.odd_of_ne_two hq2).pow)
  rw [defect_odd hn, sum_filter, sum_divisors_pow_mul_pow hp hq hpq]

/-- **Conjecture 7.1 of Chamberland and Dilcher** (with the sign of the `h*(-pq)` term corrected),
Bernoulli form. -/
theorem conj_7_1 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 3)
    (α β : ℕ) :
    S (p ^ α * q ^ β) = (((p ^ α * q ^ β : ℕ) : ℚ) - (p ^ (α / 2) * q ^ (β / 2) : ℕ)) / 2 -
      geom q ((β + 1) / 2) * ((geom p (α / 2 + 1) - jacobiSym p q * geom p (α / 2)) * hB q +
        geom p ((α + 1) / 2) * hB (p * q)) := by
  have hpq : p ≠ q := by rintro rfl; omega
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hq2 : q ≠ 2 := by rintro rfl; omega
  have h4 : p * q % 4 = 3 := by rw [Nat.mul_mod, hp4, hq4]
  have hmod : ∀ a b, p ^ a * q ^ b % 4 = 3 ↔ b % 2 = 1 := by
    intro a b
    rw [Nat.mul_mod, pow_mod_four_one hp4, pow_mod_four_three hq4]
    split_ifs <;> simp_all
  rw [S_eq_sub_defect, s_pow_mul_pow hp hq hpq, divisor_sum_pow_mul_pow hp hq hpq hp2 hq2]
  congr 1
  rw [sum_comm, sum_range_parity _ β]
  have hev : ∑ j ∈ range (β / 2 + 1), ∑ a ∈ range (α + 1),
      (if p ^ a * q ^ (2 * j) % 4 = 3 then G (p ^ a * q ^ (2 * j)) else 0) = 0 := by
    apply sum_eq_zero
    intro j _
    apply sum_eq_zero
    intro a _
    rw [ite_eq_right]
    rw [hmod]
    omega
  rw [hev, zero_add, geom, sum_mul]
  apply sum_congr rfl
  intro j _
  have hall : ∀ a, (if p ^ a * q ^ (2 * j + 1) % 4 = 3 then G (p ^ a * q ^ (2 * j + 1)) else 0) =
      G (p ^ a * q ^ (2 * j + 1)) := fun a => ite_eq_left ((hmod _ _).2 (by omega))
  simp only [hall]
  rw [sum_range_parity _ α]
  simp only [G_even_odd hp hq hpq hp2 hq4, G_odd_odd hp hq hpq h4]
  rw [← sum_mul, sum_tower, show (α + 1) / 2 = (α + 1) / 2 from rfl]
  have : ∑ i ∈ range ((α + 1) / 2), ((p : ℚ) ^ i * q ^ j * hB (p * q)) =
      geom p ((α + 1) / 2) * (q ^ j * hB (p * q)) := by
    rw [geom, sum_mul]
    apply sum_congr rfl
    intros
    ring
  rw [this]
  ring

/-- **Conjecture 7.2 of Chamberland and Dilcher**, Bernoulli form. -/
theorem conj_7_2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp4 : p % 4 = 3)
    (hq4 : q % 4 = 3) (α β : ℕ) :
    S (p ^ α * q ^ β) = (((p ^ α * q ^ β : ℕ) : ℚ) - (p ^ (α / 2) * q ^ (β / 2) : ℕ)) / 2 -
      (jacobiSym p q * geom q (β / 2) + geom q (β / 2 + 1)) * geom p ((α + 1) / 2) * hB p -
      (jacobiSym q p * geom p (α / 2) + geom p (α / 2 + 1)) * geom q ((β + 1) / 2) * hB q := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hq2 : q ≠ 2 := by rintro rfl; omega
  have hrec : jacobiSym q p = -jacobiSym p q := jacobiSym.quadratic_reciprocity_three_mod_four hq4 hp4
  have hmod : ∀ a b, p ^ a * q ^ b % 4 = 3 ↔ (a + b) % 2 = 1 := by
    intro a b
    rw [Nat.mul_mod, pow_mod_four_three hp4, pow_mod_four_three hq4]
    split_ifs <;> simp_all <;> omega
  rw [S_eq_sub_defect, s_pow_mul_pow hp hq hpq, divisor_sum_pow_mul_pow hp hq hpq hp2 hq2]
  have key : ∑ a ∈ range (α + 1), ∑ b ∈ range (β + 1),
      (if p ^ a * q ^ b % 4 = 3 then G (p ^ a * q ^ b) else 0) =
      (jacobiSym p q * geom q (β / 2) + geom q (β / 2 + 1)) * geom p ((α + 1) / 2) * hB p +
      (jacobiSym q p * geom p (α / 2) + geom p (α / 2 + 1)) * geom q ((β + 1) / 2) * hB q := by
    rw [sum_range_parity _ α]
    have hE : ∀ i, ∑ b ∈ range (β + 1),
        (if p ^ (2 * i) * q ^ b % 4 = 3 then G (p ^ (2 * i) * q ^ b) else 0) =
        (if i = 0 then (1 : ℚ) else (p : ℚ) ^ (i - 1) * (p - jacobiSym p q)) *
          geom q ((β + 1) / 2) * hB q := by
      intro i
      rw [sum_range_parity _ β]
      have h0 : ∑ j ∈ range (β / 2 + 1),
          (if p ^ (2 * i) * q ^ (2 * j) % 4 = 3 then G (p ^ (2 * i) * q ^ (2 * j)) else 0) = 0 := by
        apply sum_eq_zero
        intro j _
        rw [ite_eq_right]
        rw [hmod]
        omega
      rw [h0, zero_add, geom, mul_sum, sum_mul]
      apply sum_congr rfl
      intro j _
      rw [ite_eq_left ((hmod _ _).2 (by omega)), G_even_odd hp hq hpq hp2 hq4]
      ring
    have hO : ∀ i, ∑ b ∈ range (β + 1),
        (if p ^ (2 * i + 1) * q ^ b % 4 = 3 then G (p ^ (2 * i + 1) * q ^ b) else 0) =
        (p : ℚ) ^ i * hB p *
          ∑ j ∈ range (β / 2 + 1),
            (if j = 0 then (1 : ℚ) else (q : ℚ) ^ (j - 1) * (q - jacobiSym q p)) := by
      intro i
      rw [sum_range_parity _ β]
      have h0 : ∑ j ∈ range ((β + 1) / 2), (if p ^ (2 * i + 1) * q ^ (2 * j + 1) % 4 = 3 then
          G (p ^ (2 * i + 1) * q ^ (2 * j + 1)) else 0) = 0 := by
        apply sum_eq_zero
        intro j _
        rw [ite_eq_right]
        rw [hmod]
        omega
      rw [h0, add_zero, mul_sum]
      apply sum_congr rfl
      intro j _
      rw [ite_eq_left ((hmod _ _).2 (by omega)), mul_comm (p ^ (2 * i + 1)),
        G_even_odd hq hp hpq.symm hq2 hp4]
      ring
    simp only [hE, hO]
    have P1 : ∑ i ∈ range (α / 2 + 1), (if i = 0 then (1 : ℚ) else (p : ℚ) ^ (i - 1) *
        (p - jacobiSym p q)) * geom q ((β + 1) / 2) * hB q =
        (geom p (α / 2 + 1) - jacobiSym p q * geom p (α / 2)) * geom q ((β + 1) / 2) * hB q := by
      rw [← sum_mul, ← sum_mul, sum_tower]
    have P2 : ∀ C : ℚ, ∑ i ∈ range ((α + 1) / 2), (p : ℚ) ^ i * hB p * C =
        geom p ((α + 1) / 2) * hB p * C := by
      intro C
      rw [← sum_mul, ← sum_mul]
      rfl
    rw [P1, P2, sum_tower, hrec]
    push_cast
    ring
  rw [key]
  ring

end MeanResidue
