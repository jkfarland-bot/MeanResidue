module

public import MeanResidue

public section

/-!
# Proved solution

Every statement of `Challenge.lean` is proved, with the same name and type, in the development
`MeanResidue/` that this module imports: `MeanResidue/Lattice.lean` (Theorem 1.2 relative to the mean
residue), `MeanResidue/Count.lean` (square roots modulo an odd squarefree `n`),
`MeanResidue/Squarefree.lean` (Theorem 1.1 at odd squarefree `n`, Bernoulli form) and
`MeanResidue/Conjectures.lean` (Conjectures 7.3 and 7.4 of Chamberland and Dilcher, their formulas
(7.3), (7.4), Bunyakovsky's identity and their Proposition 1.2), `MeanResidue/PrimePower.lean` and
`MeanResidue/RootCount.lean` (square roots modulo prime powers, including `2`), `MeanResidue/Phi.lean`
(the divisor decomposition `phi` of the root count, its prime-power values and twist rule),
`MeanResidue/Lambda.lean` (the sawtooth functional and Theorem 1.1 in divisor form for every `n`),
`MeanResidue/OddPeel.lean` and `MeanResidue/EvenPeel.lean` (the values at fundamental discriminants and
the conductor recursion), `MeanResidue/TwoAdic.lean` (the `2`-adic factor), `MeanResidue/TwoPrimes.lean`
(Conjectures 7.1 and 7.2), `MeanResidue/Limits.lean` (Conjecture 7.5 from a class number bound) and
`MeanResidue/Weyl.lean` (the unconditional bound on `defect n` and Conjecture 7.5). The
definitions are those of `MeanResidue/Defs.lean`, `MeanResidue/Count.lean` (`cnt`, `cntAF`),
`MeanResidue/Conjectures.lean` (`δ`), `MeanResidue/Phi.lean` (`phiAF`, `phi`), `MeanResidue/Lambda.lean`
(`Lam`, `G`), `MeanResidue/TwoPrimes.lean` (`geom`) and `MeanResidue/EvenPeel.lean` (`kron`, `hK`,
`IsFundamental`), compared by Comparator with the copies in `Challenge.lean`, bodies included.
-/
