/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17FTA

/-!
# Sylvester's criterion: positive semidefiniteness from nonnegative principal minors

Part of the real-closed-field input to Hilbert's 17th problem for matrices
(see `Mathlib.NumberTheory.Transcendental.Hilbert17`).

Over an ordered field, a symmetric matrix is positive semidefinite (`IsPSDForm`) iff all its
principal minors are nonnegative (`isPSDForm_iff`, `isPSDForm_of_forall_principalMinor_nonneg`),
via congruence diagonalisation and a Schur-complement perturbation argument.
-/

namespace Hilbert17Blueprint

open Polynomial Matrix

/-! ### (C) Sylvester's criterion — pieces (over an ordered field) -/
section Sylvester
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
local instance : Invertible (2 : R) :=
  ⟨2⁻¹, inv_mul_cancel₀ two_ne_zero, mul_inv_cancel₀ two_ne_zero⟩

open Module in
/-- **C2-diag** (the analytic-free core of Sylvester's forward direction). Over a field of
characteristic `≠ 2`, a symmetric matrix is *congruent* to a diagonal matrix: there is an invertible
`P` and weights `w` with `Pᵀ A P = diagonal w`. **Proved** from the matrix form of
`LinearMap.BilinForm.exists_orthogonal_basis`: orthogonalise the bilinear form `x ↦ xᵀ A y`, take
`P` to be the change-of-basis matrix; in the orthogonal basis the Gram matrix `Pᵀ A P` is diagonal,
and `P` is invertible as a basis change. -/
theorem exists_congr_diagonal_of_isSymm {A : Matrix n n R} (hA : A.IsSymm) :
    ∃ (P : Matrix n n R) (w : n → R), IsUnit P.det ∧ Pᵀ * A * P = diagonal w := by
  classical
  set B : LinearMap.BilinForm R (n → R) := Matrix.toBilin' A with hBdef
  have hBsymm : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.2 hA
  obtain ⟨v0, hv0⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 hBsymm)
  have hcard : Fintype.card (Fin (Module.finrank R (n → R))) = Fintype.card n := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
  let e : Fin (Module.finrank R (n → R)) ≃ n := Fintype.equivOfCardEq hcard
  set v : Basis n R (n → R) := v0.reindex e with hvdef
  have hvortho : ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
    intro i j hij
    rw [hvdef, Basis.reindex_apply, Basis.reindex_apply]
    exact hv0 (e.symm.injective.ne hij)
  set w : n → R := fun i => B (v i) (v i) with hwdef
  have hdiag : LinearMap.BilinForm.toMatrix v B = diagonal w := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]; exact hvortho i j hij
  refine ⟨LinearMap.toMatrix v (Pi.basisFun R n) LinearMap.id, w, ?_, ?_⟩
  · rw [LinearMap.toMatrix_id_eq_basis_toMatrix]
    exact Matrix.isUnit_det_of_right_inverse
      (Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun R n) v)
  · have hc := LinearMap.BilinForm.toMatrix_comp (b := Pi.basisFun R n) (c := v)
      B LinearMap.id LinearMap.id
    rw [LinearMap.BilinForm.comp_id_id, LinearMap.BilinForm.toMatrix_basisFun, hBdef,
      LinearMap.BilinForm.toMatrix'_toBilin'] at hc
    rw [← hc, hdiag]

omit [DecidableEq n] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Congruence transports the quadratic form: `x ⬝ᵥ (Pᵀ A P) *ᵥ x = (P *ᵥ x) ⬝ᵥ A *ᵥ (P *ᵥ x)`.
**Proved.** -/
theorem congr_quadratic (A P : Matrix n n R) (x : n → R) :
    x ⬝ᵥ (Pᵀ * A * P) *ᵥ x = (P *ᵥ x) ⬝ᵥ A *ᵥ (P *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [IsStrictOrderedRing R] in
/-- **C2-weights.** In a congruence diagonalisation of a PSD form, every weight is `≥ 0` (it is the
value of the form on the corresponding column of `P`). **Proved.** -/
theorem congr_weight_nonneg {A P : Matrix n n R} {w : n → R}
    (hA : A.IsPSDForm) (hP : Pᵀ * A * P = diagonal w) (i : n) : 0 ≤ w i := by
  have key := congr_quadratic A P (Pi.single i 1)
  rw [hP] at key
  have hLHS : (Pi.single i 1 : n → R) ⬝ᵥ diagonal w *ᵥ (Pi.single i 1) = w i := by
    simp [dotProduct, mulVec_diagonal, Pi.single_apply]
  rw [hLHS] at key
  rw [key]; exact hA.2 _

/-- **C2.** The determinant of a positive semidefinite matrix is nonnegative. **Proved** from
`exists_congr_diagonal_of_isSymm`: `det P ² · det A = ∏ wᵢ ≥ 0` with `det P ≠ 0`. -/
theorem det_nonneg_of_isPSDForm {A : Matrix n n R} (hA : A.IsPSDForm) : 0 ≤ A.det := by
  obtain ⟨P, w, hPu, hP⟩ := exists_congr_diagonal_of_isSymm hA.1
  have hkey : P.det ^ 2 * A.det = ∏ i, w i := by
    have h := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_transpose, det_diagonal] at h
    linear_combination h
  have hwprod : 0 ≤ ∏ i, w i := Finset.prod_nonneg fun i _ => congr_weight_nonneg hA hP i
  have hP2 : 0 < P.det ^ 2 := (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hPu.ne_zero))
  nlinarith [hkey, hwprod, hP2]

/-- **C2'** (discriminant form). The discriminant of the quadratic form of a PSD matrix is `≥ 0`.
**Proved** from `det_nonneg_of_isPSDForm` and the (already proved) bridge `Matrix.det_eq_discr'`. -/
theorem discr'_nonneg_of_isPSDForm {A : Matrix n n R} (hA : A.IsPSDForm) :
    0 ≤ A.toQuadraticForm'.discr' := by
  rw [← Matrix.det_eq_discr' hA.1]; exact det_nonneg_of_isPSDForm hA

/-- **C3-strict** (Sylvester, strict form — the Schur-complement induction). A symmetric matrix all
of whose principal minors are *positive* is a positive semidefinite form. **Delegated** to the
dedicated from-scratch development `Matrix.isPSDForm_of_forall_principalMinor_pos` in
`Mathlib/NumberTheory/Transcendental/OrderedSylvester.lean` (its analytic core — the block quadratic
form, the Schur completing-the-square identity, and the block-PSD inductive step — is fully proved
there; only the index-type induction bookkeeping remains). -/
theorem isPSDForm_of_forall_principalMinor_pos {A : Matrix n n R} (hA : A.IsSymm)
    (hpos : ∀ s : Finset n,
      0 < (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    A.IsPSDForm :=
  Matrix.isPSDForm_of_forall_principalMinor_pos hA hpos

omit [Fintype n] [IsStrictOrderedRing R] in
/-- A principal minor along an injective index map `g` is a principal minor of `A`, hence `≥ 0`
under `hminor` (reindex `g` through its image via `det_submatrix_equiv_self`). **Proved.** -/
theorem minor_submatrix_nonneg {A : Matrix n n R}
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → n) (hg : Function.Injective g) :
    0 ≤ (A.submatrix g g).det := by
  classical
  set u : Finset n := Finset.univ.image g with hu
  have hmem : ∀ x : ι, g x ∈ u := fun x => Finset.mem_image_of_mem g (Finset.mem_univ x)
  let e : ι ≃ {x // x ∈ u} :=
    { toFun := fun x => ⟨g x, hmem x⟩
      invFun := fun y => (Finset.mem_image.1 y.2).choose
      left_inv := fun x => hg (Finset.mem_image.1 (hmem x)).choose_spec.2
      right_inv := fun y => Subtype.ext (Finset.mem_image.1 y.2).choose_spec.2 }
  have hge : g = Subtype.val ∘ e := rfl
  rw [hge, ← Matrix.submatrix_submatrix, det_submatrix_equiv_self]
  exact hminor u

/-- Positivity of `det (B + t • 1)` for `t > 0` when every principal minor of `B` is `≥ 0`:
`B + t • 1 = t • (1 + t⁻¹ • B)`, and `det (1 + t⁻¹ • B) ≥ 1` by `one_le_det_one_add_smul`.
**Proved.** -/
theorem detPosAux {m : Type*} [Fintype m] [DecidableEq m] (B : Matrix m m R)
    (hB : ∀ s' : Finset m, 0 ≤ (B.submatrix (Subtype.val : s' → m) Subtype.val).det)
    {t : R} (ht : 0 < t) : 0 < (B + t • 1).det := by
  have hfact : B + t • 1 = t • (1 + t⁻¹ • B) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul, add_comm]
  rw [hfact, det_smul]
  exact mul_pos (pow_pos ht _)
    (lt_of_lt_of_le one_pos (one_le_det_one_add_smul hB (le_of_lt (inv_pos.2 ht))))

omit [Fintype n] in
/-- **C3-perturb.** For `t > 0`, every principal minor of `A + t • 1` is *positive*, given every
principal minor of `A` is nonnegative. **Proved** from `detPosAux` + `minor_submatrix_nonneg` (the
minor equals `det (A_s + t • 1)`). -/
theorem principalMinor_add_smul_pos {A : Matrix n n R} (_hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det)
    {t : R} (ht : 0 < t) (s : Finset n) :
    0 < ((A + t • 1).submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det := by
  have hsub : (A + t • (1 : Matrix n n R)).submatrix (Subtype.val : s → n) (Subtype.val : s → n)
      = A.submatrix (Subtype.val : s → n) (Subtype.val : s → n) + t • 1 := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [show (fun i : s => (i : n)) = (Subtype.val : s → n) from rfl, hsub]
  refine detPosAux _ (fun s' => ?_) ht
  rw [Matrix.submatrix_submatrix]
  exact minor_submatrix_nonneg hminor _ (Subtype.val_injective.comp Subtype.val_injective)

/-- **C3** (reverse direction). If every principal minor is nonnegative then `A` is positive
semidefinite. **Assembly** of C3-strict + C3-perturb + the proved limit
`nonneg_of_forall_add_pos_smul`: for `t > 0`, `A + t • 1` has positive principal minors
(C3-perturb), hence is PSD (C3-strict), so `0 ≤ x ⬝ᵥ (A + t•1) *ᵥ x = x ⬝ᵥ A *ᵥ x + t • (x ⬝ᵥ x)`;
let `t → 0`. -/
theorem isPSDForm_of_forall_principalMinor_nonneg {A : Matrix n n R} (hA : A.IsSymm)
    (hminor : ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det) :
    A.IsPSDForm := by
  refine ⟨hA, fun x => ?_⟩
  have hc : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  refine nonneg_of_forall_add_pos_smul hc (fun ε hε => ?_)
  have hsymm : (A + ε • (1 : Matrix n n R)).IsSymm := by
    change (A + ε • (1 : Matrix n n R))ᵀ = A + ε • 1
    rw [transpose_add, hA.eq, transpose_smul, transpose_one]
  have h := (isPSDForm_of_forall_principalMinor_pos hsymm
    (fun s => principalMinor_add_smul_pos hA hminor hε s)).2 x
  rwa [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul] at h

/-- **Sylvester's criterion**, assembled from `Matrix.IsPSDForm.submatrix` (C1, proved), C2 and C3.
This is the proof to drop into `Matrix.isPSDForm_iff_forall_principalMinor_nonneg`. -/
theorem isPSDForm_iff {A : Matrix n n R} (hA : A.IsSymm) :
    A.IsPSDForm ↔ ∀ s : Finset n,
      0 ≤ (A.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det := by
  refine ⟨fun hpd s => ?_, isPSDForm_of_forall_principalMinor_nonneg hA⟩
  exact det_nonneg_of_isPSDForm (Matrix.IsPSDForm.submatrix hpd Subtype.val_injective)
end Sylvester

end Hilbert17Blueprint
