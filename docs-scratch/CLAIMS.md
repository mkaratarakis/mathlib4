# File ownership (concurrent sessions) — READ BEFORE WRITING ANY FILE

Several Claude sessions share this worktree.  To avoid clobbering, each file below is owned by
exactly one session.  **Never write a file you do not own.**  Before writing, re-read the file
from disk; if it changed under you, adopt the on-disk version.

All files live in `Mathlib/NumberTheory/NumberField/NormEuclidean/`.
The mathematical design is in `docs-scratch/PLAN.md`.

| file            | owner            | contents |
|-----------------|------------------|----------|
| `Norm.lean`     | DONE (compiles)  | `Algebra.dvd_norm_add_sub_pow` / `dvd_norm_sub_pow` / `dvd_norm_sub_pow_finrank` |
| `Heilbronn.lean`| session A (this) | Heilbronn's criterion: totally ramified `𝔭 ^ n = (p)`, `p = a + b`, `a` an n-th power residue, `a`, `-b` not norms ⟹ not norm-Euclidean |
| `Dumas.lean`    | session A (this) | Eisenstein–Dumas ⟹ irreducible + `p` totally ramified (`e = n`, `v_𝔭(θ) = m`) |
| `DegreeOne.lean`| session A (this) | no root mod `q` ⟹ no degree-one prime over `q` ⟹ `v_q(N α) ≠ 1` (this is the *corrected* Lemma 2.3) |
| `Counting.lean` | session B        | master box-counting lemma: per-coordinate moduli, two-sided sandwich, density limit |
| `Rootless.lean` | session C        | `#{monic deg n over 𝔽_q with no root} = Σ (-1)^k C(q,k) q^{n-k}`, closed form for `n ≥ q`, bounds `1/4 ≤ C_q(n) ≤ (q-1)/(2q)` |
| `Density.lean`  | session A (this) | assembly: master density theorem + 2/27 + `1 − ε(p)` |
| `Character.lean`| session A (this) | Theorem 1.3 conditional on Pólya–Vinogradov |

Everything must compile with `lake env lean <file>` and finally `lake build`.
NO new definitions: no `def`, `structure`, `abbrev`, `instance` — carry hypotheses instead.
