module

public import MeanResidue.Lattice
public import MeanResidue.Squarefree

@[expose] public section

/-!
# The conjectures of Chamberland and Dilcher at odd squarefree `n` (Bernoulli form)

From the floor-sum reduction (`MeanResidue.Lattice`) and the mean residue at odd squarefree `n`
(`MeanResidue.Squarefree`):

* `conj_7_3_one`, `conj_7_3_three`: Conjecture 7.3 of Chamberland and Dilcher (arXiv:2510.04387).
* `conj_7_4`: Conjecture 7.4 (Möbius inversion).
* `S_pq`, `f_pq`: their formulas (7.3) and (7.4) for `n = pq`, `p, q ≡ 3 (mod 4)`.
* `bunyakovsky`, `f_prime_three`: Bunyakovsky's identity `f p = 0` for `p ≡ 1 (mod 4)` (no class
  numbers involved) and Chamberland and Dilcher's Proposition 1.2.

The class number enters only as `hB d = -(1/d) ∑_{a<d} a (a/d)`; that `hB d = h*(-d)` for squarefree
`d ≡ 3 (mod 4)` is Dirichlet's class number formula and is not formalized.
-/

open Finset

namespace MeanResidue

/-- For squarefree `n`, `0` is the only square root of `0` modulo `n`. -/
theorem s_squarefree {n : ℕ} (hn : Squarefree n) : s n = 1 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  unfold s
  rw [card_eq_one]
  refine ⟨0, ?_⟩
  ext k
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hk, hdvd⟩
    have : n ∣ k := hn.isRadical 2 k hdvd
    exact Nat.eq_zero_of_dvd_of_lt this hk
  · rintro rfl
    exact ⟨hn0, by simp⟩

/-- `S n = (n - 1)/2 - ∑_{d ∣ n, d ≡ 3 (4)} hB d` for odd squarefree `n` (Theorem 1.1). -/
theorem S_squarefree {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    S n = ((n : ℚ) - 1) / 2 - ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  have h := defect_squarefree hn hodd
  unfold defect at h
  rw [s_squarefree hn] at h
  push_cast at h
  linarith

/-- **Conjecture 7.3 (a)**, Bernoulli form: odd squarefree `n ≡ 1 (mod 4)`. -/
theorem conj_7_3_one {n : ℕ} (hn : Squarefree n) (h4 : n % 4 = 1) :
    f n = -(1 / 2) * ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  have hodd : Odd n := Nat.odd_iff.2 (by omega)
  rw [f_mod_four_eq_one n h4, defect_squarefree hn hodd, s_squarefree hn]
  push_cast
  ring

/-- **Conjecture 7.3 (b)**, Bernoulli form: odd squarefree `n ≡ 3 (mod 4)`. -/
theorem conj_7_3_three {n : ℕ} (hn : Squarefree n) (h4 : n % 4 = 3) :
    f n = (1 - (n : ℚ)) / 4 - (1 / 2) * ∑ d ∈ n.divisors with d % 4 = 3, hB d := by
  have hodd : Odd n := Nat.odd_iff.2 (by omega)
  rw [f_mod_four_eq_three n h4, defect_squarefree hn hodd, s_squarefree hn]
  push_cast
  ring

/-- `δ d = 1` if `d ≡ 3 (mod 4)` and `0` otherwise. -/
def δ (d : ℕ) : ℚ := if d % 4 = 3 then 1 else 0

/-- Conjecture 7.3 in one formula: `(1 - d)/2 δ(d) - 2 f(d) = ∑_{e ∣ d} δ(e) hB(e)`. -/
theorem conj_7_3_combined {d : ℕ} (hd : Squarefree d) (hodd : Odd d) :
    (1 - (d : ℚ)) / 2 * δ d - 2 * f d = ∑ e ∈ d.divisors, δ e * hB e := by
  have hsum : ∑ e ∈ d.divisors, δ e * hB e = ∑ e ∈ d.divisors with e % 4 = 3, hB e := by
    rw [sum_filter]
    apply sum_congr rfl
    intro e _
    unfold δ
    split_ifs <;> ring
  rw [hsum]
  have h4 : d % 4 = 1 ∨ d % 4 = 3 := by rcases hodd with ⟨k, rfl⟩; omega
  rcases h4 with h | h
  · rw [conj_7_3_one hd h]
    unfold δ
    rw [if_neg (by omega)]
    ring
  · rw [conj_7_3_three hd h]
    unfold δ
    rw [if_pos h]
    ring

/-- Möbius inversion of a divisor sum, in the form needed here. -/
theorem moebius_inversion (g : ℕ → ℚ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℚ) * ∑ e ∈ d.divisors, g e = g n := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := g)
    (g := fun m => ∑ e ∈ m.divisors, g e)).1 (fun _ _ => rfl) n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℚ) *
    ∑ e ∈ b.divisors, g e)] at h
  exact h

/-- **Conjecture 7.4**, Bernoulli form: for odd squarefree `n`,
`hB(n) δ(n) = ∑_{d ∣ n} μ(n/d) ((1 - d)/2 δ(d) - 2 f(d))`. -/
theorem conj_7_4 {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    hB n * δ n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius (n / d) : ℚ) * ((1 - (d : ℚ)) / 2 * δ d - 2 * f d) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  rw [sum_congr rfl (fun d hd => by
    rw [conj_7_3_combined (hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
      (Odd.of_dvd_nat hodd (Nat.dvd_of_mem_divisors hd))]),
    moebius_inversion (fun e => δ e * hB e) hn0]
  ring

/-- **Bunyakovsky's identity**: `f p = 0` for primes `p ≡ 1 (mod 4)`. -/
theorem bunyakovsky {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) : f p = 0 := by
  rw [conj_7_3_one hp.squarefree h4, hp.divisors]
  have : ({1, p} : Finset ℕ).filter (· % 4 = 3) = ∅ := by
    ext d
    simp only [mem_filter, mem_insert, mem_singleton, notMem_empty, iff_false, not_and]
    rintro (rfl | rfl) <;> omega
  rw [this, sum_empty, mul_zero]

/-- **Chamberland–Dilcher, Proposition 1.2**, Bernoulli form: `f p = (1 - p)/4 - hB(p)/2` for primes
`p ≡ 3 (mod 4)`. -/
theorem f_prime_three {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) :
    f p = (1 - (p : ℚ)) / 4 - hB p / 2 := by
  rw [conj_7_3_three hp.squarefree h4, hp.divisors]
  have : ({1, p} : Finset ℕ).filter (· % 4 = 3) = {p} := by
    ext d
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · omega
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, h4⟩
  rw [this, sum_singleton]
  ring

/-- Divisors of `pq` that are `≡ 3 (mod 4)`, for distinct primes `p, q ≡ 3 (mod 4)`. -/
theorem divisors_pq_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) :
    (p * q).divisors.filter (· % 4 = 3) = {p, q} := by
  rw [Nat.divisors_mul, hp.divisors, hq.divisors]
  ext d
  simp only [mem_filter, mem_mul, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, h⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · omega
    · right; ring
    · left; ring
    · exfalso
      rw [Nat.mul_mod] at h
      rw [hp4] at h
      omega
  · rintro (rfl | rfl)
    · exact ⟨⟨d, Or.inr rfl, 1, Or.inl rfl, by ring⟩, hp4⟩
    · exact ⟨⟨1, Or.inl rfl, d, Or.inr rfl, by ring⟩, hq4⟩

/-- **Chamberland–Dilcher (7.3)**, Bernoulli form: `S_{pq} = (pq - 1)/2 - hB p - hB q`. -/
theorem S_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) :
    S (p * q) = ((p * q : ℕ) - 1 : ℚ) / 2 - hB p - hB q := by
  have hsq : Squarefree (p * q) :=
    Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_primes hp hq).2 hpq, hp.squarefree, hq.squarefree⟩
  have hodd : Odd (p * q) := Nat.odd_mul.2 ⟨Nat.odd_iff.2 (by omega), Nat.odd_iff.2 (by omega)⟩
  rw [S_squarefree hsq hodd, divisors_pq_three hp hq hpq hp4 hq4, sum_pair hpq]
  ring

/-- **Chamberland–Dilcher (7.4)**, Bernoulli form: `f(pq) = -(hB p + hB q)/2`. -/
theorem f_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) :
    f (p * q) = -(hB p + hB q) / 2 := by
  have hsq : Squarefree (p * q) :=
    Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_primes hp hq).2 hpq, hp.squarefree, hq.squarefree⟩
  have h4 : p * q % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]
  rw [conj_7_3_one hsq h4, divisors_pq_three hp hq hpq hp4 hq4, sum_pair hpq]
  ring

end MeanResidue
