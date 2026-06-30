/-
# Benchmark: our reflection *decision* tactics vs. the other repos

This measures the **proof-by-reflection** tactics — `mv_decide` / `poly_decide` (kernel, axiom-free) —
not the runtime computation benchmarked in `mvpolyCompare.lean`. The honest field of competitors here
is different from there:

* **WuProver / MonomialOrderedPolynomial** *is* the direct competitor: it is also a kernel
  proof-by-reflection decision procedure for `MvPolynomial` identities (via its `SortedRepr` + a
  `decide`). So `mv_decide` vs WuProver's `decide +kernel` is an apples-to-apples comparison.
* **CompPoly** is a *calculator*, **not** a prover — it has no tactic that proves `MvPolynomial`
  identities. So it does not compete on this axis (its computation is benchmarked separately in
  `mvpolyCompare.lean`).

## Methodology

We use Lean's built-in `profiler`, which reports per-command times *within one process*, so the
(large, noisy) import-load time is excluded and only the proof work is measured. **Both** tactics use
`decide +kernel`, so the work lands in the **type-checking** phase (pure kernel reduction); that is
the quantity reported, head-to-head. Workload: commutativity `f·g = g·f` (forces computing both
products, then a compare) for `f = (Σxᵢ+1)^p`, `g = (Σxᵢ+2)^p`, over `ZMod 7`.

## Results (`decide +kernel`; kernel type-check time; lower is better)

| identity (`ZMod 7`)            | `mv_decide` (ours) | WuProver | ours is     |
|--------------------------------|--------------------|----------|-------------|
| `(x+y+1)²·(x+y+2)²` (deg 4)    |     ≈ 0.13 s       | ≈ 0.33 s | 2.5× faster |
| `(x+y+1)³·(x+y+2)³` (deg 6)    |     ≈ 0.64 s       | ≈ 1.23 s | 1.9× faster |

**Conclusion: ours is ≈ 2× faster than WuProver** on this kernel-decide workload, and **both are
axiom-free** (only `propext`/`Classical.choice`/`Quot.sound`; no `Lean.ofReduceBool`). Two sources:

1. **Representation.** Our `List (MvDegrees × R)` with *dense-array* exponents reduces faster in the
   kernel than WuProver's sparse `SortedFinsupp`-of-`(var, exp)`-pairs — our raw kernel reduction at
   deg 4 is ≈ 128 ms vs WuProver's ≈ 303 ms (~2.3×).
2. **Idiom.** We switched our tactics to `decide +kernel`, dropping the redundant elaborator
   pre-reduction that plain `decide` pays on top of the kernel check.

(Univariate `poly_decide` at degree 10 is ≈ 0.09 s.)

## Honest caveats
* Different toolchains (ours `v4.32`, WuProver `v4.29`) — minor kernel differences.
* Same idiom now: both use `decide +kernel`, so the comparison is kernel type-checking time directly.
* Kernel reduction is the interpreter, so both are for small/medium goals; for large goals use the
  native `mv_compute` (faster, but not axiom-free).
* The representation advantage is largest at **low variable counts** (dense beats sparse); for many
  variables with low degree the gap would narrow.

Run our side: `lake env lean Mathlib/NumberTheory/Transcendental/mvpolyDecideBench.lean`
(the `set_option profiler true` lines below reprint our numbers). The WuProver reproduction script is
at the bottom.
-/
import Mathlib.NumberTheory.Transcendental.mvpolyReflectKernel
import Mathlib.NumberTheory.Transcendental.polyReflectKernel

namespace MvPolyDecideBench

open MvPolynomial

-- M2: bivariate, degree 4
set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 2 * (X 0 + X 1 + 2) ^ 2 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 2 * (X 0 + X 1 + 1) ^ 2 := by mv_decide

-- M3: bivariate, degree 6
set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 3 * (X 0 + X 1 + 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 3 * (X 0 + X 1 + 1) ^ 3 := by mv_decide

-- univariate (sub-threshold for the default profiler; lower the threshold to see it)
set_option profiler true in
set_option profiler.threshold 1 in
example : ((Polynomial.X + 1) ^ 5 * (Polynomial.X + 2) ^ 5 : Polynomial (ZMod 7))
    = (Polynomial.X + 2) ^ 5 * (Polynomial.X + 1) ^ 5 := by poly_decide

end MvPolyDecideBench

/-
## Reproducing the WuProver side

In a `MonomialOrderedPolynomial` checkout (pins `leanprover/lean4:v4.29.0-rc8`), after
`lake exe cache get` + `lake build`, run `lake env lean` on:

```
import MonomialOrderedPolynomial.MvPolynomial
open MvPolynomial
set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 2 * (X 0 + X 1 + 2) ^ 2 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 2 * (X 0 + X 1 + 1) ^ 2 := by
  rw [MvPolynomial.SortedRepr.eq_iff']; decide +kernel
set_option profiler true in
example : ((X 0 + X 1 + 1) ^ 3 * (X 0 + X 1 + 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 7))
    = (X 0 + X 1 + 2) ^ 3 * (X 0 + X 1 + 1) ^ 3 := by
  rw [MvPolynomial.SortedRepr.eq_iff']; decide +kernel
```

(Sum the reported `tactic execution` and `type checking` times; the second example is the deg-6 row.)
-/
