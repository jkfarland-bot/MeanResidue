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
(7.3), (7.4), Bunyakovsky's identity and their Proposition 1.2), and `MeanResidue/PrimePower.lean`
(square roots of units modulo odd prime powers). The definitions are those of
`MeanResidue/Defs.lean`, `MeanResidue/Count.lean` (`cnt`) and `MeanResidue/Conjectures.lean` (`δ`),
compared by Comparator with the copies in `Challenge.lean`, bodies included.
-/
