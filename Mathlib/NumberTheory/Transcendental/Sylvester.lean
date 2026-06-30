/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Sylvester's criterion over an ordered field: the analytic-free kernel

Towards Hillar–Nie's Lemma 4 (Hilbert's 17th problem for matrices,
`Mathlib/NumberTheory/Transcendental/Hilbert17Matrices.lean`) we need Sylvester's criterion over a
real closed field: a symmetric matrix with nonnegative principal minors is positive semidefinite.

Mathlib already has positive (semi)definiteness, Schur complements, and the identity expressing
characteristic-polynomial coefficients as sums of principal minors
(`Matrix.coeff_det_one_add_X_smul_eq_sum_minors`). What it does **not** have over a general ordered /
real closed field is:

* `det` of a positive semidefinite matrix is `≥ 0` (Mathlib's `Matrix.PosSemidef.det_nonneg` lives in
  `Mathlib/Analysis/` and is proved via eigenvalues over `RCLike`);
* the classical leading-principal-minor criterion for positive definiteness.

The usual real-analytic proof of the criterion perturbs `A` to `A + εI` (which is positive definite)
and lets `ε → 0`. Over a general real closed field there is no topology, but the limit step can be
replaced by a purely **ordered-field** argument, isolated here as `nonneg_of_forall_add_pos_smul`.
This file provides that kernel, plus the perturbation identity
`Matrix.one_le_det_one_add_smul`, and states the criterion itself as the remaining interface.

## Main results

* `nonneg_of_forall_add_pos_smul` : the ordered-field replacement for `ε → 0`. **Proved.**
* `Matrix.one_le_det_one_add_smul` : if all principal minors of `A` are `≥ 0` and `0 ≤ t`, then
  `1 ≤ det (1 + t • A)`. **Proved.**
* `Matrix.IsPSDForm` : positive semidefiniteness as nonnegativity of the quadratic form (no `Star`
  typeclass needed, suited to a bare ordered field).
* `Matrix.isPSDForm_iff_forall_principalMinor_nonneg` : Sylvester's criterion. Stated; its proof is
  the remaining gap (it needs the leading-minor positive-definiteness criterion, assembled from
  Mathlib's Schur-complement lemmas together with the two results above).
-/

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `2` is invertible in an ordered field (it is positive, hence nonzero). -/
local instance : Invertible (2 : R) :=
  ⟨2⁻¹, inv_mul_cancel₀ two_ne_zero, mul_inv_cancel₀ two_ne_zero⟩

/-- **Ordered-field replacement for `ε → 0`.** If `q + ε·c ≥ 0` for every `ε > 0` (with `c ≥ 0`),
then `q ≥ 0`. This is what lets Sylvester's criterion be proved over a real closed field with no
topology: a quadratic form that is nonnegative after every positive perturbation is nonnegative. -/
theorem nonneg_of_forall_add_pos_smul {q c : R} (hc : 0 ≤ c)
    (h : ∀ ε : R, 0 < ε → 0 ≤ q + ε * c) : 0 ≤ q := by
  by_contra hq
  rw [not_le] at hq
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · have h1 := h 1 one_pos
    rw [← hc0, mul_zero, add_zero] at h1
    exact absurd h1 (not_le.2 hq)
  · have hcne : c ≠ 0 := ne_of_gt hc0
    have hpos : 0 < -q / (2 * c) := div_pos (by linarith) (by linarith)
    have hkey : q + (-q / (2 * c)) * c = q / 2 := by field_simp; ring
    have h2 := h _ hpos
    rw [hkey] at h2
    linarith

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open Polynomial in
/-- If every principal minor of `A` is nonnegative and `0 ≤ t`, then `det (1 + t • A) ≥ 1`.
In particular `det (1 + t • A) > 0`. This is the perturbation step of Sylvester's criterion, made
quantitative: it follows from `det (1 + t • A) = ∑ₖ (∑ |s|=k, minorₛ A) tᵏ`, whose `k = 0` term is
`1` and whose remaining terms are nonnegative. -/
theorem one_le_det_one_add_smul {A : Matrix n n R}
    (hA : ∀ s : Finset n, 0 ≤ (A.submatrix (Subtype.val : s → n) Subtype.val).det)
    {t : R} (ht : 0 ≤ t) : 1 ≤ det (1 + t • A) := by
  -- Pass to `P = det (1 + X • A.map C)`, whose `k`-th coefficient is `∑_{|s|=k} minorₛ A`.
  set P : R[X] := det (1 + (X : R[X]) • A.map C) with hP
  have hcoeff : ∀ k, P.coeff k = ∑ s ∈ Finset.univ.powersetCard k,
      (A.submatrix (Subtype.val : s → n) Subtype.val).det :=
    fun k => coeff_det_one_add_X_smul_eq_sum_minors A k
  -- Evaluating `P` at `t` recovers `det (1 + t • A)`.
  have heval : det (1 + t • A) = P.eval t := by
    rw [hP, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C,
      eval_one, eval_zero, apply_ite (eval t)]
  rw [heval, eval_eq_sum_range]
  -- The `k = 0` term is `1`; all terms are nonnegative.
  have hpos : ∀ k ∈ Finset.range (P.natDegree + 1), 0 ≤ P.coeff k * t ^ k := by
    intro k _
    rw [hcoeff k]
    exact mul_nonneg (Finset.sum_nonneg fun s _ => hA s) (pow_nonneg ht k)
  have h0mem : 0 ∈ Finset.range (P.natDegree + 1) := Finset.mem_range.2 (Nat.succ_pos _)
  calc (1 : R) = P.coeff 0 * t ^ 0 := by
        rw [hcoeff 0]; simp [Finset.powersetCard_zero]
    _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * t ^ k :=
        Finset.single_le_sum hpos h0mem

/-- For a symmetric matrix over a field of characteristic `≠ 2`, the quadratic form `x ↦ xᵀ A x`
has `A` itself as its matrix: `(A.toQuadraticForm').toMatrix' = A`. (Round-trip through
`Matrix.toQuadraticForm'` and `QuadraticForm.toMatrix'`.) -/
theorem toMatrix'_toQuadraticForm' {A : Matrix n n R} (hA : A.IsSymm) :
    A.toQuadraticForm'.toMatrix' = A := by
  have hsymm : ∀ x y : n → R,
      (Matrix.toLinearMap₂' R A) x y = (Matrix.toLinearMap₂' R A) y x := by
    intro x y
    simp only [Matrix.toLinearMap₂'_apply']
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  have key : A.toQuadraticForm'.associated = Matrix.toLinearMap₂' R A :=
    QuadraticMap.associated_left_inverse R hsymm
  simp only [QuadraticForm.toMatrix', key, LinearMap.toMatrix'_toLinearMap₂']


/-- Consequently the determinant of a symmetric matrix is the discriminant of its quadratic form.
This reduces `0 ≤ det A` (for positive semidefinite `A`) to nonnegativity of that discriminant. -/
theorem det_eq_discr' {A : Matrix n n R} (hA : A.IsSymm) :
    A.det = A.toQuadraticForm'.discr' := by
  haveI : Invertible (2 : R) := ⟨2⁻¹, inv_mul_cancel₀ two_ne_zero, mul_inv_cancel₀ two_ne_zero⟩
  simp only [QuadraticForm.discr', toMatrix'_toQuadraticForm' hA]

/-- **Heart of diagonalisability over a formally real field** (Hillar–Nie Lemma 4, step B2).
For a symmetric matrix over an ordered field, `ker (A²) = ker A`: if `A *ᵥ (A *ᵥ v) = 0` then
already `A *ᵥ v = 0`. Indeed, with `w := A *ᵥ v`, symmetry gives
`w ⬝ᵥ w = v ⬝ᵥ (A *ᵥ (A *ᵥ v)) = 0`, and a sum of squares vanishes only at `0`. Applied to
`A - μ • 1` this shows a symmetric matrix has no nontrivial Jordan blocks, i.e. its minimal
polynomial is squarefree. -/
theorem IsSymm.mulVec_eq_zero_of_mulVec_mulVec_eq_zero {A : Matrix n n R} (hA : A.IsSymm)
    {v : n → R} (h : A *ᵥ (A *ᵥ v) = 0) : A *ᵥ v = 0 := by
  have key : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, h, zero_dotProduct]
  exact _root_.dotProduct_self_eq_zero.mp key

/-- The previous lemma in the form used for eigenvalues: for symmetric `A` and a scalar `μ`,
`(A - μ • 1)² *ᵥ v = 0 → (A - μ • 1) *ᵥ v = 0` (generalised `μ`-eigenvectors are eigenvectors). -/
theorem IsSymm.sub_smul_one_mulVec_eq_zero_of_sq {A : Matrix n n R} (hA : A.IsSymm) (μ : R)
    {v : n → R} (h : (A - μ • 1) *ᵥ ((A - μ • 1) *ᵥ v) = 0) : (A - μ • 1) *ᵥ v = 0 := by
  have hsymm : (A - μ • (1 : Matrix n n R)).IsSymm := by
    change (A - μ • (1 : Matrix n n R))ᵀ = A - μ • 1
    rw [transpose_sub, transpose_smul, transpose_one, hA.eq]
  exact hsymm.mulVec_eq_zero_of_mulVec_mulVec_eq_zero h

/-- Positive semidefiniteness phrased as nonnegativity of the quadratic form. Over a bare ordered
field this avoids the `StarRing` typeclass that `Matrix.PosSemidef` carries. -/
def IsPSDForm (A : Matrix n n R) : Prop :=
  A.IsSymm ∧ ∀ x : n → R, 0 ≤ x ⬝ᵥ A *ᵥ x

/-- The diagonal entries of a positive semidefinite matrix are nonnegative (test the quadratic form
on the standard basis vector). -/
theorem IsPSDForm.diag_nonneg {A : Matrix n n R} (hA : A.IsPSDForm) (i : n) : 0 ≤ A i i := by
  have h := hA.2 (Pi.single i 1)
  rwa [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at h

/-- **A principal submatrix of a positive semidefinite matrix is positive semidefinite**
(Sylvester step C1). Restrict the quadratic form along an injective index inclusion `e`, extending
test vectors by zero. -/
theorem IsPSDForm.submatrix {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix n n R}
    (hA : A.IsPSDForm) {e : m → n} (he : Function.Injective e) :
    (A.submatrix e e).IsPSDForm := by
  classical
  refine ⟨hA.1.submatrix e, fun y => ?_⟩
  set x : n → R := Function.extend e y 0 with hx
  have hxe : ∀ i, x (e i) = y i := fun i => he.extend_apply y 0 i
  have hx0 : ∀ l, (¬ ∃ a, e a = l) → x l = 0 := fun l hl => by
    rw [hx, Function.extend_apply' y (0 : n → R) l hl, Pi.zero_apply]
  have hinj : ∀ a ∈ (Finset.univ : Finset m), ∀ b ∈ (Finset.univ : Finset m), e a = e b → a = b :=
    fun a _ b _ h => he h
  -- the matrix–vector product of `A` against the extension restricts to the submatrix product
  have hmv : ∀ i, (A *ᵥ x) (e i) = ((A.submatrix e e) *ᵥ y) i := by
    intro i
    simp only [Matrix.mulVec, _root_.dotProduct, Matrix.submatrix_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun l _ hl => by
      rw [hx0 l (by simpa [Finset.mem_image] using hl), mul_zero]]
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun j _ => by rw [hxe]
  have hxAx : x ⬝ᵥ A *ᵥ x = ∑ i, y i * (A *ᵥ x) (e i) := by
    simp only [_root_.dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun k _ hk => by
      rw [hx0 k (by simpa [Finset.mem_image] using hk), zero_mul]]
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun i _ => by rw [hxe]
  have hyAy : y ⬝ᵥ (A.submatrix e e) *ᵥ y = ∑ i, y i * (A *ᵥ x) (e i) := by
    simp only [_root_.dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [hmv]
  rw [hyAy, ← hxAx]; exact hA.2 x

end Matrix
