# MeanResidue

Lean 4 / Mathlib formalization, stage one, of the proof of the conjectures of M. Chamberland and
K. Dilcher (*Sums of the floor function related to class numbers of imaginary quadratic fields*,
arXiv:2510.04387, Section 7) in J. S. Farland, *Mean quadratic residues, floor sums of square roots,
and class numbers* (draft, 2026).

For `n ≥ 1` put `S n = (1/n) ∑_{k<n} Rem(k² ÷ n)`, `f n = ∑_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ - (n² - 1)/12`,
`s n = #{k < n : n ∣ k²}`, `defect n = (n - s n)/2 - S n`, and `hB d = -(1/d) ∑_{a<d} a (a/d)` with the
Jacobi symbol (for squarefree `d ≡ 3 (mod 4)`, `hB d` is the weighted class number `h*(-d)` by
Dirichlet's formula). Proved:

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

Prior work. The formula for `S n` behind all of this (Theorem 1.1 of the draft, for every `n`) is the case
`a = 1` of Proposition A.2 of N.-P. Skoruppa and D. Zagier, *Jacobi forms and a certain space of modular forms*,
Invent. Math. 94 (1988), and was recorded in the form `∑_{k≤n} (k² mod n) = n(n - m)/2 - 2n ∑ h(D)/w(D)` in OEIS
A048153 by O. Kutal (2026). The proof formalized here for odd squarefree `n` is the elementary one (root counts by
Jacobi symbols and the pairing `b ↦ n - b`). The derivation of Chamberland and Dilcher's conjectures from the
formula is the new part.

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

- Dirichlet's class number formula `hB d = h*(-d)` (Mathlib has no class numbers of binary quadratic
  forms or of imaginary quadratic orders), and the conductor formula for orders.
- Theorem 1.1 for non-squarefree or even `n`; Conjectures 7.1 and 7.2 (prime powers `p^α q^β`) and
  Conjecture 7.5 (limits, which also need the bound `h*(-c) ≪ √c log c`).
