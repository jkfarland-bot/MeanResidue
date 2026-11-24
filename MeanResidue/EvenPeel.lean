module

public import MeanResidue.TwoAdic

@[expose] public section

/-!
# Theorem 1.1 for every `n ≥ 1`: fundamental discriminants and the conductor recursion

Let `kron c a` be the Kronecker symbol `(-c/a)` for `c ≡ 0, 3 (mod 4)` (computed with Jacobi symbols:
`(a/c)` for odd `c`, `χ₄(a) (c/a)` for even `c`) and `hK c = -(1/c) ∑_{a<c} a (-c/a)`. Then
* `G c = hK c` whenever `-c` is a fundamental discriminant (`G_fundamental`);
* `G (ℓ² c) = (ℓ - (-c/ℓ)) G c` for every prime `ℓ` and `c > 0` with `c ≡ 0, 3 (mod 4)` (`G_conductor`);
* `G d = 0` for `d ≡ 1, 2 (mod 4)` (Lambda.lean), and `defect n = ∑_{d ∣ n} G d` (Lambda.lean).

With Dirichlet's class number formula (`hK c = h*(-c)` for fundamental `-c`) and the conductor formula
`h*(ℓ² D) = (ℓ - (D/ℓ)) h*(D)` (both quoted), this is Theorem 1.1: `G c = h*(-c)` for every
`c ≡ 0, 3 (mod 4)`, so `(n - s(n))/2 - S_n = ∑_{c ∣ n, c ≡ 0, 3 (4)} h*(-c)`.
-/

open Finset

namespace MeanResidue

/-- The Kronecker symbol `(-c/a)`, for `c ≡ 0, 3 (mod 4)` and `a ≥ 1`. -/
def kron (c a : ℕ) : ℤ := if c % 2 = 1 then jacobiSym a c else ZMod.χ₄ a * jacobiSym c a

/-- Bernoulli form of `h*(-c)` for a fundamental discriminant `-c`. -/
def hK (c : ℕ) : ℚ := -(∑ a ∈ range c, (a : ℚ) * kron c a) / c

/-- `-c` is a fundamental discriminant. -/
def IsFundamental (c : ℕ) : Prop :=
  ∃ m, Squarefree m ∧ ((c = m ∧ m % 4 = 3) ∨ (c = 4 * m ∧ (m % 4 = 1 ∨ m % 4 = 2)))

theorem hK_odd {c : ℕ} (hc : c % 2 = 1) : hK c = hB c := by
  unfold hK hB kron
  simp only [ite_eq_left hc]

/-! ### Reciprocity bookkeeping -/

theorem jacobi_recip {c ℓ : ℕ} (hc : c % 2 = 1) (hℓ : ℓ % 2 = 1) :
    (jacobiSym c ℓ : ℚ) = (if c % 4 = 1 then 1 else (ZMod.χ₄ ℓ : ℚ)) * jacobiSym ℓ c := by
  have hco : Odd c := Nat.odd_iff.2 hc
  have hℓo : Odd ℓ := Nat.odd_iff.2 hℓ
  by_cases h1 : c % 4 = 1
  · rw [ite_eq_left h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hℓo]
  · rw [ite_eq_right h1]
    have h3 : c % 4 = 3 := by omega
    by_cases hl : ℓ % 4 = 1
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hco hl, ZMod.χ₄_nat_one_mod_four hl]
      push_cast
      ring
    · have hl3 : ℓ % 4 = 3 := by omega
      rw [jacobiSym.quadratic_reciprocity_three_mod_four h3 hl3, ZMod.χ₄_nat_three_mod_four hl3]
      push_cast
      ring

theorem jacobi_two_pow_mul (k : ℕ) {c ℓ : ℕ} (hℓ : ℓ % 2 = 1) :
    (jacobiSym ((2 : ℤ) ^ k * c) ℓ : ℚ) = (ZMod.χ₈ ℓ : ℚ) ^ k * jacobiSym c ℓ := by
  rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two (Nat.odd_iff.2 hℓ)]
  push_cast
  ring

theorem chi4_nat_sq {ℓ : ℕ} (hℓ : ℓ % 2 = 1) : (ZMod.χ₄ ℓ : ℚ) ^ 2 = 1 := by
  have := chi4_sq (ℓ := (ℓ : ℤ)) (by omega)
  simpa using this

theorem chi8_nat_sq {ℓ : ℕ} (hℓ : ℓ % 2 = 1) : (ZMod.χ₈ ℓ : ℚ) ^ 2 = 1 := by
  have := chi8_sq (ℓ := (ℓ : ℤ)) (by omega)
  simpa using this

/-! ### The odd part of `phi` at even `c` -/

theorem coprime_two_pow {c : ℕ} (hc : Odd c) (j : ℕ) : Nat.Coprime (2 ^ j) c :=
  Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hc)

theorem od_phi_even (k : ℕ) {c : ℕ} (hc : Odd c) (b : ℤ) :
    od (fun x => (phi (2 ^ (k + 2) * c) x : ℚ)) b =
      (phi c b : ℚ) * (if c % 4 = 1 then od (A (k + 2)) b else ev (A (k + 2)) b) := by
  unfold od ev A
  dsimp only
  rw [phi_mul (coprime_two_pow hc _), phi_mul (coprime_two_pow hc _), phi_neg hc]
  by_cases h1 : c % 4 = 1
  · rw [ite_eq_left h1, ZMod.χ₄_nat_one_mod_four h1]
    push_cast
    ring
  · have h3 : c % 4 = 3 := by have := Nat.odd_iff.1 hc; omega
    rw [ite_eq_right h1, ZMod.χ₄_nat_three_mod_four h3]
    push_cast
    ring

/-- **The odd-part twist** at even `c = 2^(k+2) c'`: `od φ_c (ℓ b) = (-c/ℓ) od φ_c b` for odd primes
`ℓ ∤ c`. -/
theorem od_phi_even_twist (k : ℕ) {c : ℕ} (hc : Odd c) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓc : ¬ ℓ ∣ c) (b : ℤ) :
    od (fun x => (phi (2 ^ (k + 2) * c) x : ℚ)) (ℓ * b) =
      (kron (2 ^ (k + 2) * c) ℓ : ℚ) * od (fun x => (phi (2 ^ (k + 2) * c) x : ℚ)) b := by
  have hℓo : ℓ % 2 = 1 := Nat.odd_iff.1 (hℓ.odd_of_ne_two hℓ2)
  have hcop : IsCoprime (ℓ : ℤ) c := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓc)
  have hkron : kron (2 ^ (k + 2) * c) ℓ = ZMod.χ₄ ℓ * jacobiSym ((2 ^ (k + 2) * c : ℕ) : ℤ) ℓ := by
    unfold kron
    rw [ite_eq_right (by rw [Nat.mul_mod, pow_succ]; simp)]
  obtain ⟨he, ho⟩ := A_twist (ℓ := (ℓ : ℤ)) (by omega) k
  have h8 := chi8_nat_sq hℓo
  have h4 := chi4_nat_sq hℓo
  rw [od_phi_even k hc, od_phi_even k hc, phi_twist hc hcop, hkron]
  push_cast
  rw [jacobi_two_pow_mul (k + 2) hℓo, jacobi_recip (Nat.odd_iff.1 hc) hℓo]
  by_cases h1 : c % 4 = 1
  · simp only [ite_eq_left h1]
    rw [ho]
    push_cast
    rw [show (ZMod.χ₈ ℓ : ℚ) ^ (k + 2) = (ZMod.χ₈ ℓ : ℚ) ^ k * (ZMod.χ₈ ℓ : ℚ) ^ 2 by ring, h8]
    ring
  · simp only [ite_eq_right h1]
    rw [he]
    push_cast
    rw [show (ZMod.χ₈ ℓ : ℚ) ^ (k + 2) = (ZMod.χ₈ ℓ : ℚ) ^ k * (ZMod.χ₈ ℓ : ℚ) ^ 2 by ring, h8,
      show (ZMod.χ₄ ℓ : ℚ) * ((ZMod.χ₈ ℓ : ℚ) ^ k * 1 * ((ZMod.χ₄ ℓ : ℚ) * jacobiSym ℓ c)) =
        (ZMod.χ₄ ℓ : ℚ) ^ 2 * (ZMod.χ₈ ℓ : ℚ) ^ k * jacobiSym ℓ c by ring, h4]
    ring

/-! ### The recursions at even `c` -/

/-- Peeling an odd prime `ℓ ∤ c` from even `c ≡ 0 (mod 4)`. -/
theorem G_peel_even_coprime (k : ℕ) {c : ℕ} (hc : Odd c) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓc : ¬ ℓ ∣ c) :
    G (ℓ ^ 2 * (2 ^ (k + 2) * c)) = (ℓ - kron (2 ^ (k + 2) * c) ℓ) * G (2 ^ (k + 2) * c) := by
  set C := 2 ^ (k + 2) * c with hC
  have hC0 : 0 < C := Nat.mul_pos (pow_pos two_pos _) hc.pos
  have hℓC : ¬ ℓ ∣ C := by
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).1 h with h' | h'
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h'))
    · exact hℓc h'
  have hcop : Nat.Coprime ℓ C := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓC
  have hcopZ : IsCoprime (ℓ : ℤ) C := Nat.isCoprime_iff_coprime.2 hcop
  have hper : ∀ b : ℤ, (fun x => (phi C x : ℚ)) (b + C) = (fun x => (phi C x : ℚ)) b :=
    phi_periodic C
  unfold G
  have h1 : (fun b => (phi (ℓ ^ 2 * C) b : ℚ)) = fun b => nu ℓ b * (phi C b : ℚ) := by
    funext b
    rw [phi_mul (Nat.Coprime.pow_left 2 hcop), Int.cast_mul, phi_sq_eq_nu hℓ hℓ2]
  have hper2 : ∀ b : ℤ, (fun b => nu ℓ b * (phi C b : ℚ)) (b + ((ℓ ^ 2 * C : ℕ) : ℤ)) =
      (fun b => nu ℓ b * (phi C b : ℚ)) b := by
    intro b
    rw [← h1]
    exact phi_periodic _ b
  rw [h1, ← Lam_od hper2]
  have h2 : od (fun b => nu ℓ b * (phi C b : ℚ)) = fun b => nu ℓ b * od (fun x => (phi C x : ℚ)) b := by
    funext b
    unfold od
    dsimp only
    rw [nu_neg]
    ring
  rw [h2]
  have hsq : ∀ b, od (fun x => (phi C x : ℚ)) ((ℓ : ℤ) ^ 2 * b) = od (fun x => (phi C x : ℚ)) b := by
    intro b
    unfold od
    dsimp only
    rw [phi_sq_mul hcopZ, show -((ℓ : ℤ) ^ 2 * b) = (ℓ : ℤ) ^ 2 * (-b) by ring, phi_sq_mul hcopZ]
  have htw := od_phi_even_twist k hc hℓ hℓ2 hℓc
  rw [Lam_peel hℓ.pos hC0 (od_periodic hper) hsq htw, Lam_od hper]

/-- Peeling `2` from `c ≡ 0 (mod 4)`. -/
theorem G_peel_two_pow (k : ℕ) {c : ℕ} (hc : Odd c) :
    G (2 ^ 2 * (2 ^ (k + 2) * c)) = 2 * G (2 ^ (k + 2) * c) := by
  have hcopZ : IsCoprime ((2 : ℕ) : ℤ) c := Nat.isCoprime_iff_coprime.2 (Nat.coprime_two_left.2 hc)
  unfold G
  have h : (fun b => (phi (2 ^ 2 * (2 ^ (k + 2) * c)) b : ℚ)) =
      fun b => (2 : ℚ) * dil 4 (fun x => (phi (2 ^ (k + 2) * c) x : ℚ)) b := by
    funext b
    rw [show 2 ^ 2 * (2 ^ (k + 2) * c) = 2 ^ (k + 4) * c by ring, phi_mul (coprime_two_pow hc _),
      Int.cast_mul]
    have hA := A_add_four k b
    unfold A at hA
    rw [hA]
    unfold dil
    dsimp only
    split_ifs with h4
    · rw [phi_mul (coprime_two_pow hc _)]
      obtain ⟨t, rfl⟩ := h4
      push_cast
      rw [Int.mul_ediv_cancel_left _ (by norm_num), show (4 : ℤ) * t = ((2 : ℕ) : ℤ) ^ 2 * t by norm_num,
        phi_sq_mul hcopZ]
      ring
    · ring
  rw [h, Lam_smul, show 2 ^ 2 * (2 ^ (k + 2) * c) = 4 * (2 ^ (k + 2) * c) by ring, Lam_dil (by norm_num)]

theorem exists_two_pow_mul {c : ℕ} (hc0 : c ≠ 0) (h4 : c % 4 = 0) :
    ∃ k c', Odd c' ∧ c = 2 ^ (k + 2) * c' := by
  obtain ⟨e, c', hc', hce⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 2 (by norm_num)
  have hodd : Odd c' := Nat.odd_iff.2 (by omega)
  have he : 2 ≤ e := by
    by_contra h
    interval_cases e
    · rw [pow_zero, one_mul] at hce
      rw [hce] at h4
      have := Nat.odd_iff.1 hodd
      omega
    · rw [pow_one] at hce
      rw [hce] at h4
      have := Nat.odd_iff.1 hodd
      omega
  exact ⟨e - 2, c', hodd, by rw [hce, show e - 2 + 2 = e by omega]⟩

theorem G_zero : G 0 = 0 := by
  simp [G, Lam]

/-- **The conductor recursion**: `G (ℓ² c) = (ℓ - (-c/ℓ)) G c` for every prime `ℓ` and every
`c > 0` with `c ≡ 0, 3 (mod 4)`. -/
theorem G_conductor {ℓ c : ℕ} (hℓ : ℓ.Prime) (hc0 : 0 < c) (hc : c % 4 = 0 ∨ c % 4 = 3) :
    G (ℓ ^ 2 * c) = (ℓ - kron c ℓ) * G c := by
  rcases hc with h0 | h3
  · obtain ⟨k, c', hc', rfl⟩ := exists_two_pow_mul hc0.ne' h0
    by_cases h2 : ℓ = 2
    · subst h2
      have hk : kron (2 ^ (k + 2) * c') 2 = 0 := by
        unfold kron
        rw [ite_eq_right (by rw [Nat.mul_mod, pow_succ]; simp)]
        have : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
        rw [this, zero_mul]
      rw [G_peel_two_pow k hc', hk]
      push_cast
      ring
    · by_cases hdvd : ℓ ∣ c'
      · have hk : kron (2 ^ (k + 2) * c') ℓ = 0 := by
          unfold kron
          rw [ite_eq_right (by rw [Nat.mul_mod, pow_succ]; simp)]
          have hJ : jacobiSym ((2 ^ (k + 2) * c' : ℕ) : ℤ) ℓ = 0 := by
            rw [jacobiSym.eq_zero_iff]
            refine ⟨hℓ.ne_zero, ?_⟩
            rw [Int.gcd_natCast_natCast, Nat.gcd_eq_right (dvd_mul_of_dvd_right hdvd _)]
            exact hℓ.one_lt.ne'
          push_cast at hJ
          push_cast
          rw [hJ, mul_zero]
        rw [G_peel_dvd hℓ h2 hc0.ne' (dvd_mul_of_dvd_right hdvd _), hk]
        push_cast
        ring
      · exact G_peel_even_coprime k hc' hℓ h2 hdvd
  · have hk : kron c ℓ = jacobiSym ℓ c := by
      unfold kron
      rw [ite_eq_left (by omega)]
    rw [hk, G_peel hℓ h3]

/-! ### Fundamental discriminants -/

theorem jacobi_four {a : ℕ} (ha : a % 2 = 1) : jacobiSym (4 : ℤ) a = 1 := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
  apply jacobiSym.sq_one'
  apply Int.isCoprime_iff_gcd_eq_one.1
  exact (Int.prime_two.coprime_iff_not_dvd).2 (by omega)

/-- `G (4m) = hK (4m)` for squarefree `m ≡ 1 (mod 4)`. -/
theorem G_four_mul {m : ℕ} (hm : Squarefree m) (h1 : m % 4 = 1) : G (4 * m) = hK (4 * m) := by
  have hmo : Odd m := Nat.odd_iff.2 (by omega)
  have hpos : 0 < 4 * m := Nat.mul_pos (by norm_num) hmo.pos
  have hper := phi_periodic (4 * m)
  unfold G
  rw [← Lam_od hper, Lam_odd hpos (od_periodic hper) (od_neg _), hK]
  congr 2
  apply sum_congr rfl
  intro a _
  have e := od_phi_even 0 hmo a
  rw [show 2 ^ (0 + 2) * m = 4 * m by ring, ite_eq_left h1, od_A_two, phi_squarefree hm hmo] at e
  have hk : kron (4 * m) a = ZMod.χ₄ a * jacobiSym ((4 * m : ℕ) : ℤ) a := by
    unfold kron
    rw [ite_eq_right (by omega)]
  rw [e, hk]
  congr 1
  by_cases ha : a % 2 = 1
  · push_cast
    rw [jacobiSym.mul_left, jacobi_four ha, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.2 ha)]
    ring
  · have h4 : ZMod.χ₄ ((a : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.χ₄_int_eq_if_mod_four, ite_eq_left (by omega)]
    simp only [Int.cast_natCast] at h4
    push_cast
    rw [h4]
    simp

/-- `G (8m) = hK (8m)` for odd squarefree `m`. -/
theorem G_eight_mul {m : ℕ} (hm : Squarefree m) (hmo : Odd m) : G (8 * m) = hK (8 * m) := by
  have hpos : 0 < 8 * m := Nat.mul_pos (by norm_num) hmo.pos
  have hper := phi_periodic (8 * m)
  have hm2 : m % 2 = 1 := Nat.odd_iff.1 hmo
  unfold G
  rw [← Lam_od hper, Lam_odd hpos (od_periodic hper) (od_neg _), hK]
  congr 2
  apply sum_congr rfl
  intro a _
  have e := od_phi_even 1 hmo a
  rw [show 2 ^ (1 + 2) * m = 8 * m by ring, show (1 : ℕ) + 2 = 3 from rfl,
    phi_squarefree hm hmo] at e
  have hk : kron (8 * m) a = ZMod.χ₄ a * jacobiSym ((8 * m : ℕ) : ℤ) a := by
    unfold kron
    rw [ite_eq_right (by omega)]
  rw [e, hk]
  congr 1
  by_cases ha : a % 2 = 1
  · have hJ := jacobi_two_pow_mul 3 (c := m) ha
    rw [show (2 : ℤ) ^ 3 * m = 8 * (m : ℤ) by norm_num, jacobi_recip hm2 ha] at hJ
    push_cast
    rw [hJ]
    have h8 := chi8_nat_sq ha
    have h4 := chi4_nat_sq ha
    by_cases h1 : m % 4 = 1
    · rw [ite_eq_left h1, ite_eq_left h1, od_A_three, chi8'_eq]
      simp only [Int.cast_natCast]
      rw [show (ZMod.χ₈ a : ℚ) ^ 3 = (ZMod.χ₈ a : ℚ) * (ZMod.χ₈ a : ℚ) ^ 2 by ring, h8]
      ring
    · rw [ite_eq_right h1, ite_eq_right h1, ev_A_three]
      simp only [Int.cast_natCast]
      rw [show (ZMod.χ₈ a : ℚ) ^ 3 = (ZMod.χ₈ a : ℚ) * (ZMod.χ₈ a : ℚ) ^ 2 by ring, h8]
      rw [show (jacobiSym a m : ℚ) * (ZMod.χ₈ a : ℚ) =
          (ZMod.χ₄ a : ℚ) ^ 2 * (ZMod.χ₈ a : ℚ) * jacobiSym a m by rw [h4]; ring]
      ring
  · have h4 : ZMod.χ₄ ((a : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.χ₄_int_eq_if_mod_four, ite_eq_left (by omega)]
    have h8 : ZMod.χ₈ ((a : ℤ) : ZMod 8) = 0 := by
      rw [ZMod.χ₈_int_eq_if_mod_eight, ite_eq_left (by omega)]
    have h8' : ZMod.χ₈' ((a : ℤ) : ZMod 8) = 0 := by
      rw [ZMod.χ₈'_int_eq_if_mod_eight, ite_eq_left (by omega)]
    simp only [Int.cast_natCast] at h4 h8 h8'
    push_cast
    rw [h4]
    split_ifs
    · rw [od_A_three]
      simp only [Int.cast_natCast]
      rw [h8']
      simp
    · rw [ev_A_three]
      simp only [Int.cast_natCast]
      rw [h8]
      simp

/-- **Fundamental discriminants**: `G c = hK c` whenever `-c` is a fundamental discriminant
(Dirichlet's class number formula identifies `hK c` with `h*(-c)`; quoted). -/
theorem G_fundamental {c : ℕ} (hc : IsFundamental c) : G c = hK c := by
  obtain ⟨m, hm, (⟨rfl, h3⟩ | ⟨rfl, h1 | h2⟩)⟩ := hc
  · rw [G_squarefree hm h3, hK_odd (by omega)]
  · exact G_four_mul hm h1
  · obtain ⟨m', rfl⟩ : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have hm' : Squarefree m' := hm.of_mul_right
    have hm'o : Odd m' := by
      rcases Nat.even_or_odd m' with ⟨t, ht⟩ | h
      · exfalso
        rw [ht] at h2
        omega
      · exact h
    rw [show 4 * (2 * m') = 8 * m' by ring]
    exact G_eight_mul hm' hm'o

end MeanResidue
