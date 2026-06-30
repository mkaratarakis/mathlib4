/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17Lemma4

/-!
# Hilbert's 17th problem for matrices — capstone

This file ties together the development of the matrix analogue of Artin's theorem, following
Hillar–Nie, *An elementary and constructive solution to Hilbert's 17th problem for matrices*
(arXiv:math/0610388):

> **Theorem (Hillar–Nie, Theorem 3).** Let `F` be a formally real field and `A` a symmetric matrix
> over `F`. If every principal minor of `A` is a sum of squares in `F`, then `A` is a sum of squares
> of symmetric matrices over `F`.

The end-to-end statement is `hilbert17_for_matrices` below. The development is complete and
`sorry`-free; `hilbert17_for_matrices` depends only on Mathlib's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Architecture (files in this directory)

* `ArtinSchreier.lean` — the easy Artin–Schreier theorem in both directions: in a formally real
  field an element is a sum of squares iff it is nonnegative in every ordering
  (`RingPreordering.isSumSq_of_forall_mem`), built from a self-contained development of the
  sum-of-squares preordering, adjoining an element, and Zorn-extension of a preordering to an
  ordering. Also the order induced on a field by an ordering (`RingPreordering.toLinearOrder`).

* `Sylvester.lean`, `OrderedSylvester.lean` — the ordered-field kernel of Sylvester's criterion:
  positive semidefiniteness as nonnegativity of the quadratic form, principal-submatrix
  monotonicity, and the perturbation/Schur-complement machinery establishing that nonnegative
  principal minors imply positive semidefiniteness.

* `Hilbert17Blueprint.lean` — the real-closed-field spectral theory. The algebraic fundamental
  theorem of algebra (`R[i]` algebraically closed), the spectral theorem over a real closed field
  (the minimal polynomial of a symmetric matrix splits with nonnegative roots), the **existence of
  a real closure of an ordered field** (`exists_realClosure`, via a weighted-sums-of-squares Zorn
  argument), and the resulting **transfer** that the signed coefficients of `minpoly F A` are sums
  of squares with nonzero linear term (`isSumSq_minpoly_signedCoeff`, `minpoly_coeff_one_ne_zero`).

* `Hilbert17Matrices.lean` — the matrix algebra: `Matrix.IsSumSqSymm`, the engine
  `Matrix.isSumSqSymm_of_factor`, and the signed characteristic-polynomial coefficients as sums of
  squares.

* `Hilbert17Lemma4.lean` — Hillar–Nie's **identity (1)** and **Lemma 4**. From the Lemma-4 shape of
  `minpoly F A` it builds `B = ∑_{i odd} aᵢ Aⁱ⁻¹`, `R = ∑_{i even} aᵢ Aⁱ` in the commutative algebra
  `F[A]`, proves `A·B = R` (Cayley–Hamilton, parity split), that `B`, `R` are sums of squares, and —
  without real closed fields — that `B` is invertible (its quadratic form is anisotropic over the
  formally real field `F`), assembling `A = B·(B⁻²R)`. Lemma 4 itself (`minpoly_lemma4`) is supplied
  by the spectral theory in `Hilbert17Blueprint.lean`.
-/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

/-- **Hilbert's 17th problem for matrices (Hillar–Nie, Theorem 3).**
Let `F` be a formally real field and `A` a symmetric matrix over `F` all of whose principal minors
are sums of squares in `F`. Then `A` is a sum of squares of symmetric matrices over `F`.

This is the end-to-end statement of the development; see the module docstring for the proof
architecture. -/
theorem hilbert17_for_matrices [IsSemireal F] {A : Matrix n n F} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      IsSumSq (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    A.IsSumSqSymm :=
  Hilbert17Lemma4.isSumSqSymm_of_principalMinors hA hminor
