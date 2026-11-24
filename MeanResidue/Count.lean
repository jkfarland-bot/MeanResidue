module

public import MeanResidue.Defs

@[expose] public section

/-!
# Square roots modulo `n`

`cnt n a` is the number of square roots of `a` modulo `n`. It is multiplicative in `n` (Chinese
remainder theorem), equals `1 + (a/p)` at an odd prime `p` (Mathlib's `quadraticChar_card_sqrts`), and
hence equals `∑_{d ∣ n} (a/d)` for every odd squarefree `n`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace MeanResidue

/-- The number of square roots of `a` modulo `n`. -/
noncomputable def cnt (n : ℕ) (a : ℤ) : ℕ := Nat.card {x : ZMod n // x ^ 2 = (a : ZMod n)}

theorem cnt_one (a : ℤ) : cnt 1 a = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, Subsingleton.elim _ _⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩

theorem cnt_mul {m n : ℕ} (h : m.Coprime n) (a : ℤ) : cnt (m * n) a = cnt m a * cnt n a := by
  unfold cnt
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  refine ((e.toEquiv.subtypeEquiv (q := fun y : ZMod m × ZMod n => y ^ 2 = (a : ZMod m × ZMod n))
    (fun x => ?_)).trans (Equiv.subtypeEquivRight (fun y => ?_))).trans Equiv.subtypeProdEquivProd
  · show x ^ 2 = (a : ZMod (m * n)) ↔ (e x) ^ 2 = (a : ZMod m × ZMod n)
    rw [← map_pow, ← map_intCast e]
    exact e.injective.eq_iff.symm
  · show y ^ 2 = (a : ZMod m × ZMod n) ↔ y.1 ^ 2 = (a : ZMod m) ∧ y.2 ^ 2 = (a : ZMod n)
    rw [Prod.ext_iff, Prod.pow_fst, Prod.pow_snd, Prod.fst_intCast, Prod.snd_intCast]

theorem cnt_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (a : ℤ) :
    (cnt p a : ℤ) = 1 + jacobiSym a p := by
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← jacobiSym.legendreSym.to_jacobiSym]
  have h := quadraticChar_card_sqrts (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) (a : ZMod p)
  rw [Set.toFinset_ofPred] at h
  rw [h]
  unfold legendreSym
  ring

/-- `cnt` as a multiplicative arithmetic function. -/
noncomputable def cntAF (a : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (cnt n a : ℤ), by simp⟩

theorem cntAF_apply (a : ℤ) {n : ℕ} (hn : n ≠ 0) : cntAF a n = cnt n a := by
  simp [cntAF, hn]

theorem isMultiplicative_cntAF (a : ℤ) : (cntAF a).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn hmn => ?_⟩
  · rw [cntAF_apply a one_ne_zero, cnt_one]; rfl
  · rw [cntAF_apply a (mul_ne_zero hm hn), cntAF_apply a hm, cntAF_apply a hn, cnt_mul hmn]
    push_cast; ring

/-- The Jacobi symbol `d ↦ (a/d)` as a multiplicative arithmetic function. -/
def jacAF (a : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun d => if d = 0 then 0 else jacobiSym a d, by simp⟩

theorem jacAF_apply (a : ℤ) {d : ℕ} (hd : d ≠ 0) : jacAF a d = jacobiSym a d := by
  simp [jacAF, hd]

theorem isMultiplicative_jacAF (a : ℤ) : (jacAF a).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn _ => ?_⟩
  · rw [jacAF_apply a one_ne_zero, jacobiSym.one_right]
  · have : NeZero m := ⟨hm⟩
    have : NeZero n := ⟨hn⟩
    rw [jacAF_apply a (mul_ne_zero hm hn), jacAF_apply a hm, jacAF_apply a hn,
      jacobiSym.mul_right]

/-- For odd squarefree `n`, the number of square roots of `a` modulo `n` is `∑_{d ∣ n} (a/d)`. -/
theorem cnt_eq_sum_jacobi {n : ℕ} (hn : Squarefree n) (hodd : Odd n) (a : ℤ) :
    (cnt n a : ℤ) = ∑ d ∈ n.divisors, jacobiSym a d := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hmul : (jacAF a * (ζ : ArithmeticFunction ℤ)).IsMultiplicative :=
    (isMultiplicative_jacAF a).mul isMultiplicative_zeta.natCast
  have h1 : cntAF a n = (jacAF a * (ζ : ArithmeticFunction ℤ)) n := by
    rw [IsMultiplicative.multiplicative_factorization _ (isMultiplicative_cntAF a) hn0,
      IsMultiplicative.multiplicative_factorization _ hmul hn0]
    apply Finsupp.prod_congr
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.factorization_eq_one_of_squarefree hn hpp hpn, pow_one]
    have := Fact.mk hpp
    have hp2 : p ≠ 2 := by
      intro h2
      have := Odd.of_dvd_nat hodd hpn
      rw [h2] at this
      exact absurd this (by decide)
    rw [coe_mul_zeta_apply, hpp.divisors, Finset.sum_pair hpp.one_lt.ne, cntAF_apply a hpp.ne_zero,
      cnt_prime p hp2 a, jacAF_apply a one_ne_zero, jacAF_apply a hpp.ne_zero, jacobiSym.one_right]
  rw [cntAF_apply a hn0, coe_mul_zeta_apply] at h1
  rw [h1]
  apply sum_congr rfl
  intro d hd
  exact jacAF_apply a (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))

end MeanResidue
