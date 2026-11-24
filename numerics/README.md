# Numerical checks

Python scripts for the numerical verification in Section 8 of J. S. Farland, *Mean quadratic residues,
floor sums of square roots, and class numbers: the conjectures of Chamberland and Dilcher*, preprint,
Zenodo, 2026, [doi:10.5281/zenodo.24508994](https://doi.org/10.5281/zenodo.24508994). They check selected
statements of the note over the finite ranges listed below, independently of the Lean formalization.
The class numbers `h(D)` are computed by counting reduced primitive binary quadratic forms, so no
`L`-function and no class number formula is used. The identities are checked in exact rational
arithmetic (Python `fractions`); the checks that involve complex exponentials (Gauss sums, the cotangent
sums of Skoruppa and Zagier, the Fourier coefficients of Proposition 5.3) and partial sums of `L(1, D)`
use floating point.

Requirements: Python 3 and NumPy. The scripts can be run from any directory; `cd1` to `cd4` import the
shared module `cd_lib.py` from this folder. Each `cdN_out.txt` is the output of `cdN_*.py` with the
default ranges.

| Script | What it checks | Output |
|---|---|---|
| `cd1_verify.py` | Theorems 1.1 and 1.2 for every `n ≤ 20000` | `cd1_out.txt` |
| `cd2_conjectures.py` | Conjecture 7.1 as printed and with the corrected sign, Conjectures 7.2, 7.3 and 7.4, and `f(n)/n` near the limits of Conjecture 7.5 | `cd2_out.txt` |
| `cd3_lemmas.py` | Lemmas 2.2 (Gauss sums), 2.3 (Jacobi and Kronecker symbols) and 2.4 (class numbers of orders, through partial sums of `L(1, D)`), and Corollary 1.3(d) for `n ≤ 6000` | `cd3_out.txt` |
| `cd4_skoruppa_zagier.py` | Theorem 1.1 against Proposition A.2 of Skoruppa and Zagier (case `a = 1`) for `f ≤ 400` | `cd4_out.txt` |
| `cd5_second_proof.py` | Section 6 (the second proof of Theorem 1.1) for `d ≤ 2000`, and Proposition 5.3 for `n ≤ 20000` | `cd5_out.txt` |

```
python3 numerics/cd1_verify.py
python3 numerics/cd2_conjectures.py
python3 numerics/cd3_lemmas.py
python3 numerics/cd4_skoruppa_zagier.py
python3 numerics/cd5_second_proof.py
```

The range of `cd_lib.py` is set by the environment variable `CD_NMAX` (default `20000`), and `cd1_verify.py`
also takes it as its first argument; `cd2` and `cd3` assume the default. The ranges of `cd5_second_proof.py`
are set by `CD5_N` (default `2000`) and `CD5_NB` (default `20000`). With the defaults, `cd1` to `cd4` take a
few seconds each and `cd5` about a minute.
