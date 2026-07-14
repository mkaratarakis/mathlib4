/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Block triangular unitary matrices are block diagonal

A unitary matrix cannot be "genuinely" triangular: since the inverse of a unitary matrix `M` is
its star-transpose, and the inverse of a block triangular matrix is block triangular
(`Matrix.blockTriangular_inv_of_blockTriangular`), a block triangular unitary matrix must also
be block triangular in the opposite direction. Concretely, if a unitary matrix `M` is block
triangular with respect to `b : m → α`, then `M i j = 0` as soon as `b i ≠ b j`. In particular
a unitary matrix which is block triangular with respect to an injective `b` is diagonal
(`Matrix.BlockTriangular.isDiag_of_mem_unitaryGroup`).

This fact appears in the Schur triangularization argument ([horn2013], Section 2.3): a normal
triangular matrix is diagonal. It reduces QR-type factorizations of unitary matrices to
factorizations with a diagonal remainder, as in
`Mathlib/Analysis/Matrix/GivensRotation.lean`.
-/

@[expose] public section

namespace Matrix

variable {α m R : Type*} [CommRing R] [StarRing R] [Fintype m] [DecidableEq m]
variable [LinearOrder α] {M : Matrix m m R} {b : m → α}

namespace BlockTriangular

/-- The entries of a block triangular unitary matrix vanish as soon as the values of the
blocking function differ. -/
theorem apply_eq_zero_of_mem_unitaryGroup (hM : BlockTriangular M b)
    (hU : M ∈ unitaryGroup m R) {i j : m} (h : b i ≠ b j) : M i j = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have : Invertible M := ⟨star M, hU.1, hU.2⟩
    have h0 : star M j i = 0 :=
      (inv_eq_right_inv hU.2 ▸ blockTriangular_inv_of_blockTriangular hM) hlt
    rwa [star_apply, star_eq_zero] at h0
  · exact hM hlt

/-- A block triangular unitary matrix with an injective blocking function is diagonal. -/
theorem isDiag_of_mem_unitaryGroup (hM : BlockTriangular M b) (hU : M ∈ unitaryGroup m R)
    (hb : Function.Injective b) : M.IsDiag := fun _ _ hij =>
  hM.apply_eq_zero_of_mem_unitaryGroup hU fun h => hij (hb h)

end BlockTriangular

end Matrix
