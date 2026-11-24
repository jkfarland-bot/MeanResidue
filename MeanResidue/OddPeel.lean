module

public import MeanResidue.Lambda

@[expose] public section

/-!
# Odd `n`: the conductor recursion

For `c ≡ 3 (mod 4)` and every prime `ℓ`,
`G (ℓ² c) = (ℓ - (ℓ/c)) G c`   (`G_peel`),
and `G c = hB c` for squarefree `c ≡ 3 (mod 4)` (`G_squarefree`). Since `(ℓ/c)` is the Kronecker symbol
`(-c/ℓ)`, this is the conductor formula `h*(ℓ² D) = (ℓ - (D/ℓ)) h*(D)` for the discriminants `D = -c`,
and with Dirichlet's formula `hB c₀ = h*(-c₀)` it identifies `G c` with `h*(-c)` for every odd
`c ≡ 3 (mod 4)`.

The engine is `Lam_peel`: if `g` is periodic modulo `m`, invariant under `b ↦ q² b` and multiplied by
`λ` under `b ↦ q b`, then `Lam (q² m) (ν_q g) = (q - λ) Lam m g` with `ν_q(b) = q [q² ∣ b] - [q ∣ b]`.
-/

open Finset

namespace MeanResidue

/-- `ν_q(b) = q [q² ∣ b] - [q ∣ b]` (this is `phi (q²) b` for odd `q`). -/
def nu (q : ℕ) (b : ℤ) : ℚ :=
  (if (q : ℤ) ^ 2 ∣ b then (q : ℚ) else 0) - (if (q : ℤ) ∣ b then 1 else 0)

/-- The dilation `b ↦ [q ∣ b] g(b/q)`. -/
def dil (q : ℕ) (g : ℤ → ℚ) (b : ℤ) : ℚ := if (q : ℤ) ∣ b then g (b / q) else 0

theorem Lam_dil {q m : ℕ} (hq : 0 < q) (g : ℤ → ℚ) : Lam (q * m) (dil q g) = Lam m g :=
  Lam_dilate hq g

theorem dil_periodic {q m : ℕ} (hq : 0 < q) {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b) (b : ℤ) :
    dil q g (b + (q * m : ℕ)) = dil q g b := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold dil
  push_cast
  by_cases h : (q : ℤ) ∣ b
  · obtain ⟨c, rfl⟩ := h
    rw [ite_eq_left (dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)), ite_eq_left (dvd_mul_right _ _),
      show (q : ℤ) * c + q * m = q * (c + m) by ring, Int.mul_ediv_cancel_left _ hq0,
      Int.mul_ediv_cancel_left _ hq0, hg]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    exact h ((dvd_add_left (dvd_mul_right _ _)).1 h')

/-- **The peeling lemma.** -/
theorem Lam_peel {q m : ℕ} (hq : 0 < q) (hm : 0 < m) {g : ℤ → ℚ} (hg : ∀ b, g (b + m) = g b)
    (hsq : ∀ b, g ((q : ℤ) ^ 2 * b) = g b) {l : ℚ} (htw : ∀ b, g (q * b) = l * g b) :
    Lam (q ^ 2 * m) (fun b => nu q b * g b) = (q - l) * Lam m g := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq20 : (q : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have h1 : (fun b => nu q b * g b) = fun b => (q : ℚ) * dil (q ^ 2) g b - l * dil q g b := by
    funext b
    unfold nu dil
    push_cast
    by_cases h2 : (q : ℤ) ^ 2 ∣ b
    · have h1' : (q : ℤ) ∣ b := (dvd_pow_self _ two_ne_zero).trans h2
      rw [ite_eq_left h2, ite_eq_left h1', ite_eq_left h2, ite_eq_left h1']
      obtain ⟨c, rfl⟩ := h2
      obtain ⟨c', hc'⟩ := h1'
      rw [Int.mul_ediv_cancel_left _ hq20, hsq]
      have : (q : ℤ) ^ 2 * c / q = q * c := by
        rw [show (q : ℤ) ^ 2 * c = q * (q * c) by ring, Int.mul_ediv_cancel_left _ hq0]
      have hll : l * (l * g c) = g c := by
        rw [← htw, ← htw, ← hsq c]
        congr 1
        ring
      rw [this, htw, hll]
      ring
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h1 : (q : ℤ) ∣ b
      · rw [ite_eq_left h1, ite_eq_left h1]
        obtain ⟨c, rfl⟩ := h1
        rw [Int.mul_ediv_cancel_left _ hq0, htw]
        ring
      · rw [ite_eq_right h1, ite_eq_right h1]
        ring
  rw [h1, Lam_sub, Lam_smul, Lam_smul]
  have e1 : Lam (q ^ 2 * m) (dil (q ^ 2) g) = Lam m g := Lam_dil (pow_pos hq 2) g
  have e2 : Lam (q ^ 2 * m) (dil q g) = Lam m g := by
    rw [show q ^ 2 * m = (q * m) * q by ring, Lam_inflate (Nat.mul_pos hq hm) hq (dil_periodic hq hg),
      Lam_dil hq g]
  rw [e1, e2]
  ring

/-- `ν_q` is `phi (q²)` for odd `q`. -/
theorem phi_sq_eq_nu {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (b : ℤ) : (phi (q ^ 2) b : ℚ) = nu q b := by
  have := Fact.mk hq
  rw [phi_sq_odd q hq2, nu]
  push_cast
  split_ifs <;> simp

/-- `phi 4 = ν₂ + χ₄`. -/
theorem phi_four_eq_nu (b : ℤ) : (phi 4 b : ℚ) = nu 2 b + ZMod.χ₄ b := by
  rw [phi_four, nu]
  push_cast
  norm_num

theorem jacobiSym_eq_zero_of_dvd {ℓ c : ℕ} (hℓ : ℓ.Prime) (hc : c ≠ 0) (h : ℓ ∣ c) :
    jacobiSym ℓ c = 0 := by
  rw [jacobiSym.eq_zero_iff]
  refine ⟨hc, ?_⟩
  rw [Int.gcd_natCast_natCast, Nat.gcd_eq_left h]
  exact hℓ.one_lt.ne'

/-- Peeling an odd prime not dividing `c`. -/
theorem G_peel_coprime {q c : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hc : Odd c) (hqc : ¬ q ∣ c) :
    G (q ^ 2 * c) = (q - jacobiSym q c) * G c := by
  have hcop : Nat.Coprime q c := (Nat.Prime.coprime_iff_not_dvd hq).2 hqc
  have hcopZ : IsCoprime (q : ℤ) c := Nat.isCoprime_iff_coprime.2 hcop
  unfold G
  have h : (fun b => (phi (q ^ 2 * c) b : ℚ)) = fun b => nu q b * (phi c b : ℚ) := by
    funext b
    rw [phi_mul (Nat.Coprime.pow_left 2 hcop), Int.cast_mul, phi_sq_eq_nu hq hq2]
  rw [h]
  have htw : ∀ b, (phi c (q * b) : ℚ) = (jacobiSym q c : ℚ) * phi c b := by
    intro b
    rw [phi_twist hc hcopZ]
    push_cast
    ring
  have hsq : ∀ b, (phi c ((q : ℤ) ^ 2 * b) : ℚ) = phi c b := by
    intro b
    rw [phi_sq_mul hcopZ]
  exact Lam_peel hq.pos hc.pos (phi_periodic c) hsq htw

/-- Peeling an odd prime dividing `c` (any `c ≠ 0`). -/
theorem G_peel_dvd {q c : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hc : c ≠ 0) (hqc : q ∣ c) :
    G (q ^ 2 * c) = q * G c := by
  have := Fact.mk hq
  obtain ⟨e, c', hc', hce⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc q hq.one_lt.ne'
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hce
    exact hc' (hce ▸ hqc)
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hcop : Nat.Coprime q c' := (Nat.Prime.coprime_iff_not_dvd hq).2 hc'
  have hcopZ : IsCoprime (q : ℤ) c' := Nat.isCoprime_iff_coprime.2 hcop
  have hq20 : (q : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hq.ne_zero)
  unfold G
  have h : (fun b => (phi (q ^ 2 * c) b : ℚ)) = fun b => (q : ℚ) * dil (q ^ 2) (fun b => (phi c b : ℚ)) b := by
    funext b
    rw [hce, show q ^ 2 * (q ^ (k + 1) * c') = q ^ (k + 3) * c' by ring,
      phi_mul (Nat.Coprime.pow_left _ hcop), phi_pow_add_two_odd q hq2]
    unfold dil
    push_cast
    by_cases h2 : (q : ℤ) ^ 2 ∣ b
    · rw [ite_eq_left h2, ite_eq_left h2, phi_mul (Nat.Coprime.pow_left _ hcop)]
      obtain ⟨t, rfl⟩ := h2
      rw [Int.mul_ediv_cancel_left _ hq20, phi_sq_mul hcopZ]
      push_cast
      ring
    · rw [ite_eq_right h2, ite_eq_right h2]
      simp
  rw [h, Lam_smul, show q ^ 2 * c = q ^ 2 * c from rfl, Lam_dil (pow_pos hq.pos 2)]

theorem chi4_neg (b : ℤ) : (ZMod.χ₄ (-b : ℤ) : ℤ) = -ZMod.χ₄ b := by
  push_cast
  have key : ∀ x : ZMod 4, ZMod.χ₄ (-x) = -ZMod.χ₄ x := by decide
  exact key _

theorem chi4_periodic (b : ℤ) (c : ℕ) : (ZMod.χ₄ ((b + ((4 * c : ℕ) : ℤ) : ℤ)) : ℤ) = ZMod.χ₄ b := by
  push_cast
  have : ((4 : ℤ) : ZMod 4) = 0 := by decide
  rw [show (4 : ZMod 4) = ((4 : ℤ) : ZMod 4) by norm_num, this, zero_mul, add_zero]

/-- Peeling `2` from `c ≡ 3 (mod 4)`. -/
theorem G_peel_two {c : ℕ} (hc : c % 4 = 3) : G (2 ^ 2 * c) = (2 - jacobiSym 2 c) * G c := by
  have hco : Odd c := Nat.odd_iff.2 (by omega)
  have hcop : Nat.Coprime 2 c := Nat.coprime_two_left.2 hco
  have hcopZ : IsCoprime ((2 : ℕ) : ℤ) c := Nat.isCoprime_iff_coprime.2 hcop
  unfold G
  have h : (fun b => (phi (2 ^ 2 * c) b : ℚ)) =
      fun b => nu 2 b * (phi c b : ℚ) + (ZMod.χ₄ b : ℚ) * phi c b := by
    funext b
    rw [phi_mul (Nat.Coprime.pow_left 2 hcop), Int.cast_mul, show (2 : ℕ) ^ 2 = 4 by norm_num,
      phi_four_eq_nu]
    ring
  rw [h, Lam_add]
  have htw : ∀ b, (phi c ((2 : ℕ) * b) : ℚ) = (jacobiSym 2 c : ℚ) * phi c b := by
    intro b
    rw [phi_twist hco hcopZ]
    push_cast
    ring
  have hsq : ∀ b, (phi c (((2 : ℕ) : ℤ) ^ 2 * b) : ℚ) = phi c b := by
    intro b
    rw [phi_sq_mul hcopZ]
  have e1 := Lam_peel (q := 2) (g := fun b => (phi c b : ℚ)) (by norm_num) hco.pos (phi_periodic c)
    hsq htw
  have e2 : Lam (2 ^ 2 * c) (fun b => (ZMod.χ₄ b : ℚ) * phi c b) = 0 := by
    apply Lam_even
    · intro b
      rw [show ((2 ^ 2 * c : ℕ) : ℤ) = ((4 * c : ℕ) : ℤ) by norm_num, chi4_periodic]
      congr 1
      push_cast
      exact_mod_cast phi_congr ⟨4, by push_cast; ring⟩
    · intro b
      rw [chi4_neg, phi_neg hco, ZMod.χ₄_nat_three_mod_four hc]
      push_cast
      ring
  rw [e1, e2]
  push_cast
  ring

/-- **The conductor recursion** at odd `c ≡ 3 (mod 4)`: `G (ℓ² c) = (ℓ - (ℓ/c)) G c` for every
prime `ℓ`. -/
theorem G_peel {ℓ c : ℕ} (hℓ : ℓ.Prime) (hc : c % 4 = 3) :
    G (ℓ ^ 2 * c) = (ℓ - jacobiSym ℓ c) * G c := by
  have hco : Odd c := Nat.odd_iff.2 (by omega)
  by_cases h2 : ℓ = 2
  · subst h2
    exact_mod_cast G_peel_two hc
  · by_cases hdvd : ℓ ∣ c
    · rw [G_peel_dvd hℓ h2 hco.pos.ne' hdvd, jacobiSym_eq_zero_of_dvd hℓ hco.pos.ne' hdvd]
      simp
    · exact G_peel_coprime hℓ h2 hco hdvd

theorem sum_jacobi_three_mod_four {c : ℕ} (h4 : c % 4 = 3) :
    ∑ b ∈ range c, (jacobiSym b c : ℚ) = 0 := by
  have hco : Odd c := Nat.odd_iff.2 (by omega)
  have h := jac_reflect c c dvd_rfl hco (fun _ => (1 : ℚ)) 1 (fun _ _ => by ring)
  have hχ : (ZMod.χ₄ c : ℚ) = -1 := by rw [ZMod.χ₄_nat_three_mod_four h4]; norm_num
  simp only [mul_one, one_mul, hχ] at h
  have hz : ∑ b ∈ Ico 1 c, (jacobiSym b c : ℚ) = 0 := by linarith
  rw [range_split c hco.pos, hz]
  simp [jacobiSym.zero_left (show 1 < c by omega)]

/-- **Base case**: `G c = hB c` for squarefree `c ≡ 3 (mod 4)`. -/
theorem G_squarefree {c : ℕ} (hc : Squarefree c) (h4 : c % 4 = 3) : G c = hB c := by
  have hco : Odd c := Nat.odd_iff.2 (by omega)
  unfold G
  have h : (fun b => (phi c b : ℚ)) = fun b => (jacobiSym b c : ℚ) := by
    funext b
    rw [phi_squarefree hc hco]
  rw [h, Lam_eq_range hco.pos, sum_jacobi_three_mod_four h4,
    jacobiSym.zero_left (show 1 < c by omega), hB]
  push_cast
  ring

end MeanResidue
