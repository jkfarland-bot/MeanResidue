# MeanResidue

Lean 4 / Mathlib formalization of the proof of the conjectures of M. Chamberland and K. Dilcher
(*Sums of the floor function related to class numbers of imaginary quadratic fields*, arXiv:2510.04387,
Section 7) in J. S. Farland, *Mean quadratic residues, floor sums of square roots, and class numbers*
(draft, 2026).

For `n ≥ 1` put `S n = (1/n) ∑_{k<n} Rem(k² ÷ n)`, `f n = ∑_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ - (n² - 1)/12`,
`s n = #{k < n : n ∣ k²}`, `defect n = (n - s n)/2 - S n`, and `hB d = -(1/d) ∑_{a<d} a (a/d)` with the
Jacobi symbol (for squarefree `d ≡ 3 (mod 4)`, `hB d` is the weighted class number `h*(-d)` by
Dirichlet's formula). Let `cnt n b` be the number of square roots of `b` modulo `n`,
`phi d b = ∑_{e ∣ d} μ(d/e) cnt(e, b)`, `Lam d g = -(1/d) ∑_{0<b<d} g(b)(b - d/2)` and
`G d = Lam d (phi d ·)`.

## Stage one

- **Theorem 1.2, for every `n`** (`f_mod_four_eq_one`, `_three`, `_zero`, `_two`):
  `f n = (s n - 1)/4 - defect n/2`, `(s n - n)/4 - defect n/2`, `n/8 + s n/4 - defect n/2`,
  `-n/8 + (s n - 1)/4 - defect n/2` for `n ≡ 1, 3, 0, 2 (mod 4)`.
- **Root count** (`cnt_eq_sum_jacobi`): for odd squarefree `n`, the number of square roots of `a`
  modulo `n` is `∑_{d ∣ n} (a/d)`.
- **Units modulo odd prime powers** (`cnt_unit`): for an odd prime `p`, `m ≥ 1` and `p ∤ u`, the number
  of square roots of `u` modulo `p^m` is `1 + (u/p)` (no Hensel lifting: the squares and the units that
  are squares modulo `p` are subgroups of index 2 of `(ℤ/p^m)ˣ`, one inside the other).
- **Theorem 1.1 at odd squarefree `n`, Bernoulli form** (`defect_squarefree`, `S_squarefree`):
  `(n - 1)/2 - S n = ∑_{d ∣ n, d ≡ 3 (4)} hB d`.
- **Chamberland–Dilcher**: Conjecture 7.3 (`conj_7_3_one`, `conj_7_3_three`), Conjecture 7.4
  (`conj_7_4`), formulas (7.3) and (7.4) for `n = pq` (`S_pq`, `f_pq`), Bunyakovsky's identity
  `f p = 0` for `p ≡ 1 (mod 4)` (`bunyakovsky`) and Proposition 1.2 (`f_prime_three`), with `hB` in
  place of `h*`.

## Stages two and three

- **Square roots modulo prime powers** (`cnt_pow_add_two_mul_sq`, `cnt_two_pow_unit`):
  `cnt (p^(i+2)) (p² b) = p cnt (p^i) b` for every prime `p`; an odd `u` has `4` square roots modulo
  `2^m` (`m ≥ 3`) if `u ≡ 1 (mod 8)` and none otherwise.
- **Theorem 1.1 for every `n`, divisor form** (`defect_eq_sum_G`): `(n - s(n))/2 - S n = ∑_{d ∣ n} G d`.
  The proof: `cnt n = ∑_{d ∣ n} phi d` (Möbius inversion), `n defect n` is the sawtooth sum of `cnt n`,
  and a function periodic modulo `d` has the same sawtooth sum at every multiple of `d`.
- **The terms `G c`**: `G c = 0` for `c ≡ 1, 2 (mod 4)` (`G_one_mod_four`, `G_two_mod_four`);
  `G c = hK c = -(1/c) ∑_{a<c} a (-c/a)` when `-c` is a fundamental discriminant (`G_fundamental`); and the
  conductor recursion `G (ℓ² c) = (ℓ - (-c/ℓ)) G c` for every prime `ℓ` and `c ≡ 0, 3 (mod 4)`
  (`G_conductor`), with the Kronecker symbol `(-c/ℓ)` computed from Jacobi symbols (`kron`). With
  Dirichlet's formula `hK c = h*(-c)` and the conductor formula `h*(ℓ² D) = (ℓ - (D/ℓ)) h*(D)` (both quoted)
  these say `G c = h*(-c)`, which is Theorem 1.1. The tools: the twist rule `phi d (x b) = (x/d) phi d b`
  for odd `d`, the even and odd parts of `phi (2^j)` (eigenfunctions of the odd twists with eigenvalues
  `χ₈^j` and `χ₄ χ₈^j`), and a peeling lemma for the sawtooth functional under dilations.
- **Möbius form** (`moebius_defect`): `∑_{d ∣ n} μ(n/d) defect(d) = G n` for every `n` (Corollary 1.3(d)).
- **Conjecture 7.1** (`conj_7_1`), with the sign of its `h*(-pq)` term corrected, and **Conjecture 7.2**
  (`conj_7_2`), for `n = p^α q^β` and all `α, β ≥ 0`, in Bernoulli form, with `[e]_ℓ = 1 + ℓ + ⋯ + ℓ^(e-1)`
  (`geom`).
- **Conjecture 7.5 from a class number bound** (`conj_7_5_of_class_number_bound`): the limits, assuming
  `|G c| ≤ C √c (1 + log c)` (the route of the note: `h*(-c) = (√c/π) L(1, -c)` and
  `|L(1, -c)| ≤ 3 + log c`), via Cauchy–Schwarz with `τ(n) ≤ 2√n` and `σ(n) ≤ n(1 + log n)`, and `s(n)² ∣ n`.

## Stage four

- **An unconditional bound** (`defect_sq_le`): `defect(n)² ≤ n √n (1 + log n)³` for every `n ≥ 1`. No class
  numbers: `-defect n = ∑_{x ∈ ℤ/n} saw(x²)` with the sawtooth `saw`; Mathlib's discrete Fourier transform on
  `ZMod n` gives `∑_x saw(x²) = (1/n) ∑_h 𝓕saw(h) G(h)` with `G(h) = ∑_x e(hx²/n)`; the coefficients are
  explicit (`𝓕saw(h) = 1/(ζ - 1) + 1/2`, `ζ = e(-h/n)`, so `‖𝓕saw(h)‖ ≤ n/(4 min(h, n - h))` by Jordan's
  inequality); Weyl differencing gives `‖G(h)‖² ≤ n gcd(2h, n)`; and the sum over `h` is bounded through
  the divisors of `n`.
- **Conjecture 7.5** (`conj_7_5`), unconditionally: `f(n)/n → 1/8, 0, -1/8, -1/4` along
  `n ≡ 0, 1, 2, 3 (mod 4)`.

Prior work. The formula for `S n` behind all of this (Theorem 1.1 of the draft, for every `n`) is the case
`a = 1` of Proposition A.2 of N.-P. Skoruppa and D. Zagier, *Jacobi forms and a certain space of modular forms*,
Invent. Math. 94 (1988), and was recorded in the form `∑_{k≤n} (k² mod n) = n(n - m)/2 - 2n ∑ h(D)/w(D)` in OEIS
A048153 by O. Kutal (2026). The proof formalized here is elementary: root counts modulo prime powers, Möbius
inversion, the twist rule and a sawtooth functional; class numbers enter only through Dirichlet's formula and the
conductor formula, which are quoted. The derivation of Chamberland and Dilcher's conjectures from the formula is the
new part.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. `Challenge.lean` states the results with `sorry`; `Solution.lean` imports the
development; Palomar's `lake comparator` accepts the pair with the Lean, nanoda and con-ron kernels.

## Not formalized

- Dirichlet's class number formula `hK c = h*(-c)` for fundamental discriminants (Mathlib has no class
  numbers of binary quadratic forms or of imaginary quadratic orders) and the conductor formula for
  orders; the formalization proves that `G` satisfies the same base values and the same recursion.
- The analytic bound `h*(-c) ≤ C √c (1 + log c)`, which enters only `conj_7_5_of_class_number_bound` as a
  hypothesis; `conj_7_5` does not need it.

## Numerical checks

The folder [`numerics/`](numerics/) holds the Python scripts behind Section 8 of the note, with their outputs.
They check the note's statements in exact rational arithmetic, with class numbers counted from reduced
forms, independently of the Lean development. They are not part of the formalization or of the comparator
check.
