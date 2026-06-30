/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17

/-!
# Sanity-check examples for Hilbert's 17th problem for matrices

Worked examples exercising `hilbert17_for_matrices` (Hillar–Nie, Theorem 3): a symmetric matrix
over a formally real field all of whose principal minors are sums of squares is a sum of squares of
symmetric matrices.

* `Matrix.IsSumSqSymm.diagonal` — a diagonal matrix with sum-of-squares entries satisfies the
  hypothesis (its principal minors are products of the entries) and hence the conclusion. This is
  the cleanest family of examples.
* concrete instances over `ℚ` (`diagonal ![1, 2]`, the identity).
* `diag_one_zero_eq_sq` — an *independent* check, with no appeal to the main theorem, that the
  conclusion is genuinely true on a small case: `diag(1, 0) = B²` for a symmetric `B`.

The examples that go *through* `hilbert17_for_matrices` exercise the (complete, `sorry`-free) main
theorem, while `diag_one_zero_eq_sq` checks the conclusion directly on a small case.
-/

open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Diagonal example.** A diagonal matrix whose diagonal entries are sums of squares is a sum of
squares of symmetric matrices: every principal minor is a product of (some of) the entries, hence a
sum of squares, so `hilbert17_for_matrices` applies. -/
theorem IsSumSqSymm.diagonal {d : n → F} (hd : ∀ i, IsSumSq (d i)) :
    (Matrix.diagonal d).IsSumSqSymm := by
  refine hilbert17_for_matrices (isSymm_diagonal d) (fun s => ?_)
  rw [submatrix_diagonal d (fun i : s => (i : n)) Subtype.val_injective, det_diagonal]
  exact IsSumSq.prod (fun i _ => hd i)

end Matrix

/-- The `2 × 2` diagonal matrix `diag(1, 2)` over `ℚ` is a sum of squares of symmetric matrices. -/
example : (Matrix.diagonal ![(1 : ℚ), 2]).IsSumSqSymm := by
  have h1 : IsSumSq (1 : ℚ) := by rw [← one_mul (1 : ℚ)]; exact IsSumSq.mul_self 1
  have h2 : IsSumSq (2 : ℚ) := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num]; exact h1.add h1
  refine Matrix.IsSumSqSymm.diagonal (fun i => ?_)
  fin_cases i
  · exact h1
  · exact h2

/-- The identity matrix over `ℚ` is a sum of squares of symmetric matrices (all its principal minors
are `1`). -/
example : (1 : Matrix (Fin 3) (Fin 3) ℚ).IsSumSqSymm := by
  rw [← Matrix.diagonal_one]
  exact Matrix.IsSumSqSymm.diagonal (fun _ => by rw [← one_mul (1 : ℚ)]; exact IsSumSq.mul_self 1)

/-- **Independent sanity check** (no use of the main theorem): the conclusion is genuinely true on a
small singular case — `diag(1, 0) = B²` with `B` symmetric, so it *is* a sum of squares of symmetric
matrices, exactly as the theorem predicts. -/
theorem diag_one_zero_eq_sq :
    (Matrix.diagonal ![(1 : ℚ), 0]) = (Matrix.diagonal ![(1 : ℚ), 0]) ^ 2 := by
  rw [sq, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i; fin_cases i <;> simp
