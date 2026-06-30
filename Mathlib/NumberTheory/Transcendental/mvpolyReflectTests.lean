/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.mvpolyReflectKernel

/-!
# Tests / demonstration of the `MvPolynomial` reflection tactics

This file is a guided tour (and a regression test) of the reflection tactic `mv_decide` (and its
synonym `mv_compute`) that proves identities and inequalities about Mathlib's **noncomputable**
`MvPolynomial` by computing on our **computable** `MvSparsePoly`. It reflects a goal `p = q` (or
`p ≠ q`) onto kernel-reducible normal forms and closes with kernel `decide +kernel` — **axiom-free**
(no `native_decide`/`ofReduceBool`); the kernel interpreter is the bottleneck, so it is for
small/medium goals. The bridge is the ring isomorphism `toPoly : MvSparsePoly R n ≃ₐ MvPolynomial`.

Run this file with `lake env lean Mathlib/NumberTheory/Transcendental/mvpolyReflectTests.lean`.
-/

open MvPolynomial

namespace MvPolyReflectTests

/-! ## 1. Basic ring identities — both tactics agree -/

-- The square of a sum, two variables. `C 2` is the constant polynomial `2`.
example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by
  mv_compute      -- native (fast)

example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by
  mv_decide       -- kernel (axiom-free)

/-! ## 2. Cancellation to zero — the normal form drops zero coefficients -/

-- Difference of squares: the `X 0 * X 1` cross terms cancel (`+1` and `−1`), so the normal form has
-- no `X 0 X 1` term at all. Both tactics handle this via `filter (·.2 ≠ 0)`.
example : ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 - X 1 ^ 2 := by mv_compute
example : ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 - X 1 ^ 2 := by mv_decide

-- A whole expression collapsing to `0`:
example : ((X 0 + X 1) ^ 2 - X 0 ^ 2 - C 2 * (X 0 * X 1) - X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) = 0 := by
  mv_decide

/-! ## 3. Factored form = expanded form -/

example : ((X 0 + X 1) ^ 2 * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ)
    = (X 0 + X 1) * (X 0 ^ 2 - X 1 ^ 2) := by mv_compute

example : ((X 0 + X 1) ^ 2 * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ)
    = (X 0 + X 1) * (X 0 ^ 2 - X 1 ^ 2) := by mv_decide

-- A 3-variable symmetric identity, `(a+b+c)^2`:
example : ((X 0 + X 1 + X 2) ^ 2 : MvPolynomial (Fin 3) ℤ)
    = X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2
      + C 2 * (X 0 * X 1) + C 2 * (X 0 * X 2) + C 2 * (X 1 * X 2) := by
  mv_decide

/-! ## 4. Inequalities — `mv_compute` only (`mv_decide` is `=`-only by design) -/

example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 0 ^ 2 + X 1 ^ 2 := by mv_compute
example : ((X 0 + X 1) ^ 3 : MvPolynomial (Fin 2) ℤ) ≠ X 0 ^ 3 + X 1 ^ 3 := by mv_compute

/-! ## 5. Different coefficient rings — `ℚ`

The native path is happy with any computable ring. The kernel path (`mv_decide`) is best for rings
whose arithmetic reduces cheaply in the kernel (`ℤ`, `ZMod`); `ℚ`'s normalized `Rat` arithmetic does
not reduce well there, so for `ℚ` we use `mv_compute`. -/

example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℚ) = X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by
  mv_compute
example : ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℚ) = X 0 ^ 2 - X 1 ^ 2 := by mv_compute

/-! ## 6. A larger goal `((Σ)^2)^2 = (Σ)^4` (kernel-decided; slower but axiom-free) -/

example : (((X 0 + X 1 + X 2) ^ 2) ^ 2 : MvPolynomial (Fin 3) ℤ)
    = (X 0 + X 1 + X 2) ^ 4 := by
  mv_decide

/-! ## 7. The trust check, made explicit

`#print axioms` shows the proof depends only on the three standard Mathlib axioms — crucially **not**
`Lean.ofReduceBool` (which `native_decide` would add and which Mathlib's `lean4checker` rejects). -/

theorem diff_of_squares : ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 - X 1 ^ 2 := by
  mv_decide

#print axioms diff_of_squares   -- [propext, Classical.choice, Quot.sound]

end MvPolyReflectTests
