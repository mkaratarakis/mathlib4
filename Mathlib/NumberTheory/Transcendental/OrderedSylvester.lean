/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sylvester
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Sylvester's criterion over an ordered field (the positive-definite direction)

Mathlib's `Matrix.PosDef`/`PosSemidef` are built on `StarRing`/`RCLike`, so they do not apply to a
bare linearly ordered field. This file develops, **from scratch over a linearly ordered field**, the
analytic core of the forward (strict) direction of Sylvester's criterion for the analytic-free
notion `Matrix.IsPSDForm` (`0 ≤ x ⬝ᵥ A *ᵥ x`), needed to discharge the `C3-strict` `sorry` of
`Hilbert17Blueprint`.

## Main results

* `Matrix.quadraticForm_fromBlocks` — the quadratic form of a `2×2` block matrix expands into its
  four block contributions. **Proved.**
* `Matrix.complete_square` — the Schur-complement *completing the square* identity:
  `xᵀ M x = (y + A'⁻¹Bt)ᵀ A' (y + A'⁻¹Bt) + tᵀ (D − Bᵀ A'⁻¹ B) t` for `x = (y, t)`. **Proved.**
* `Matrix.isPSDForm_fromBlocks_of_schur` — if the top-left block `A'` is an invertible PSD form and
  the Schur complement `D − Bᵀ A'⁻¹ B` is a PSD form, the whole symmetric block matrix is a PSD
  form. **Proved** (this is the inductive step of Sylvester's criterion).
* `Matrix.isPSDForm_of_forall_principalMinor_pos` — a symmetric matrix all of whose principal minors
  are positive is a PSD form. **Proved**, by strong induction on the index cardinality: split off
  one coordinate (`Equiv.sumCompl`), apply the inductive hypothesis to the leading block, and feed
  Schur-complement positivity (from `det_fromBlocks₁₁`) into `isPSDForm_fromBlocks_of_schur`.

This file is `sorry`-free; it fully discharges the `C3-strict` atom of `Hilbert17Blueprint`.
-/

open Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The quadratic form of a block matrix expands into its four block contributions. -/
theorem quadraticForm_fromBlocks (A' : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) (y : m → R) (t : n → R) :
    (Sum.elim y t) ⬝ᵥ (fromBlocks A' B C D) *ᵥ (Sum.elim y t)
      = y ⬝ᵥ (A' *ᵥ y) + y ⬝ᵥ (B *ᵥ t) + t ⬝ᵥ (C *ᵥ y) + t ⬝ᵥ (D *ᵥ t) := by
  simp only [fromBlocks_mulVec, sumElim_dotProduct_sumElim, dotProduct_add,
    Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

/-- The bilinear form of a symmetric matrix is symmetric: `u ⬝ᵥ A' *ᵥ v = v ⬝ᵥ A' *ᵥ u`. -/
theorem symm_dot {A' : Matrix m m R} (hA' : A'.IsSymm) (u v : m → R) :
    u ⬝ᵥ A' *ᵥ v = v ⬝ᵥ A' *ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA'.eq, dotProduct_comm, dotProduct_mulVec,
    ← mulVec_transpose, hA'.eq]

/-- **Completing the square** (Schur complement). For an invertible symmetric `A'`, the quadratic
form of the block matrix splits as an `A'`-square plus a Schur-complement term. -/
theorem complete_square {A' : Matrix m m R} (hA' : A'.IsSymm) (hinv : IsUnit A'.det)
    (B : Matrix m n R) (D : Matrix n n R) (y : m → R) (t : n → R) :
    y ⬝ᵥ (A' *ᵥ y) + y ⬝ᵥ (B *ᵥ t) + t ⬝ᵥ (Bᵀ *ᵥ y) + t ⬝ᵥ (D *ᵥ t)
      = (y + A'⁻¹ *ᵥ (B *ᵥ t)) ⬝ᵥ (A' *ᵥ (y + A'⁻¹ *ᵥ (B *ᵥ t)))
        + t ⬝ᵥ ((D - Bᵀ * A'⁻¹ * B) *ᵥ t) := by
  have e1 : (Bᵀ * A'⁻¹ * B) *ᵥ t = Bᵀ *ᵥ (A'⁻¹ *ᵥ (B *ᵥ t)) := by
    rw [mulVec_mulVec, mulVec_mulVec]
  have hAc : A' *ᵥ (A'⁻¹ *ᵥ (B *ᵥ t)) = B *ᵥ t := by
    rw [mulVec_mulVec, mul_nonsing_inv A' hinv, one_mulVec]
  have hcross2 : (A'⁻¹ *ᵥ (B *ᵥ t)) ⬝ᵥ A' *ᵥ y = y ⬝ᵥ B *ᵥ t := by rw [symm_dot hA', hAc]
  have ht2 : t ⬝ᵥ Bᵀ *ᵥ y = y ⬝ᵥ B *ᵥ t := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hcc : (A'⁻¹ *ᵥ (B *ᵥ t)) ⬝ᵥ (B *ᵥ t) = t ⬝ᵥ (Bᵀ * A'⁻¹ * B) *ᵥ t := by
    rw [e1]
    conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]
    rw [dotProduct_comm]
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, sub_mulVec, dotProduct_sub,
    hAc, hcross2, hcc, ht2]
  ring

/-- **Inductive step of Sylvester's criterion.** If `A'` is an invertible PSD form and the Schur
complement `D - Bᵀ A'⁻¹ B` is a PSD form, then the symmetric block matrix `fromBlocks A' B Bᵀ D` is
a PSD form. **Proved** from `complete_square`. -/
theorem isPSDForm_fromBlocks_of_schur {A' : Matrix m m R} (hA' : A'.IsSymm) (hinv : IsUnit A'.det)
    (hA'psd : ∀ y, 0 ≤ y ⬝ᵥ A' *ᵥ y) (B : Matrix m n R) {D : Matrix n n R} (hD : D.IsSymm)
    (hschur : ∀ t, 0 ≤ t ⬝ᵥ (D - Bᵀ * A'⁻¹ * B) *ᵥ t) :
    (fromBlocks A' B Bᵀ D).IsPSDForm := by
  refine ⟨?_, fun z => ?_⟩
  · change (fromBlocks A' B Bᵀ D)ᵀ = _
    rw [fromBlocks_transpose, hA'.eq, hD.eq, transpose_transpose]
  · rw [← Sum.elim_comp_inl_inr z, quadraticForm_fromBlocks, complete_square hA' hinv]
    exact add_nonneg (hA'psd _) (hschur _)

/-- A principal minor along an injective index map is a principal minor of `A`, hence positive
(reindex `g` through its image via `det_submatrix_equiv_self`). **Proved.** -/
theorem minor_submatrix_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι R}
    (hpos : ∀ s : Finset ι, 0 < (A.submatrix (Subtype.val : s → ι) Subtype.val).det)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (g : κ → ι) (hg : Function.Injective g) :
    0 < (A.submatrix g g).det := by
  classical
  set u : Finset ι := Finset.univ.image g with hu
  have hmem : ∀ x : κ, g x ∈ u := fun x => Finset.mem_image_of_mem g (Finset.mem_univ x)
  let e : κ ≃ {x // x ∈ u} :=
    { toFun := fun x => ⟨g x, hmem x⟩
      invFun := fun y => (Finset.mem_image.1 y.2).choose
      left_inv := fun x => hg (Finset.mem_image.1 (hmem x)).choose_spec.2
      right_inv := fun y => Subtype.ext (Finset.mem_image.1 y.2).choose_spec.2 }
  have hge : g = Subtype.val ∘ e := rfl
  rw [hge, ← Matrix.submatrix_submatrix, det_submatrix_equiv_self]
  exact hpos u

/-- `IsPSDForm` is invariant under reindexing the index type by an equivalence. **Proved.** -/
theorem isPSDForm_submatrix_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι ι R} (e : κ ≃ ι) :
    (A.submatrix e e).IsPSDForm ↔ A.IsPSDForm := by
  constructor
  · rintro ⟨hsymm, hform⟩
    refine ⟨?_, fun y => ?_⟩
    · have h := hsymm.submatrix e.symm
      rwa [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at h
    · have h := hform (y ∘ e)
      rw [submatrix_mulVec_equiv,
        show (y ∘ ⇑e) ∘ ⇑e.symm = y from by
          rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id],
        comp_equiv_dotProduct_comp_equiv] at h
      exact h
  · rintro ⟨hsymm, hform⟩
    refine ⟨hsymm.submatrix e, fun x => ?_⟩
    rw [submatrix_mulVec_equiv, ← comp_equiv_symm_dotProduct]
    exact hform _

/-- The quadratic form of a matrix over a `Unique` index type is `Sₓₓ · tₓ²`, hence nonnegative
when `det S ≥ 0`. -/
theorem form_nonneg_of_unique {κ : Type*} [Fintype κ] [DecidableEq κ] [Unique κ]
    {S : Matrix κ κ R} (h : 0 ≤ S.det) (t : κ → R) : 0 ≤ t ⬝ᵥ S *ᵥ t := by
  rw [det_unique] at h
  have : t ⬝ᵥ S *ᵥ t = S default default * (t default * t default) := by
    simp [dotProduct, mulVec, Fintype.sum_unique]; ring
  rw [this]
  exact mul_nonneg h (mul_self_nonneg _)

/-- **Sylvester's criterion, forward direction, over an ordered field.** A symmetric matrix all of
whose principal minors are positive is a positive semidefinite form.

The proof is the Schur-complement induction on the index type: peel off one coordinate, apply the
inductive hypothesis to the leading block `A'` (whose principal minors are principal minors of `A`,
hence positive — in particular `A'` is invertible), obtain Schur-complement positivity from
`Matrix.det_fromBlocks₁₁` (`det A = det A' · det (D − Bᵀ A'⁻¹ B)`, both `det A, det A' > 0`), and
conclude with `isPSDForm_fromBlocks_of_schur`. The inductive bookkeeping (reindexing the index type
to a block sum and transferring the minor hypothesis) is the remaining `sorry`. -/
theorem isPSDForm_of_forall_principalMinor_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : A.IsSymm)
    (hpos : ∀ s : Finset ι,
      0 < (A.submatrix (fun i : s => (i : ι)) (fun i : s => (i : ι))).det) :
    A.IsPSDForm := by
  suffices H : ∀ n (ι : Type _) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R), A.IsSymm →
      (∀ s : Finset ι, 0 < (A.submatrix (Subtype.val : s → ι) Subtype.val).det) →
      Fintype.card ι = n → A.IsPSDForm by
    exact H _ ι A hA hpos rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ι _ _ A hA hpos hcard
    rcases isEmpty_or_nonempty ι with hempty | hne
    · exact ⟨hA, fun x => by simp [dotProduct, Finset.univ_eq_empty]⟩
    · obtain ⟨j⟩ := hne
      classical
      set p : ι → Prop := fun i => i ≠ j with hp
      set e : {i // p i} ⊕ {i // ¬ p i} ≃ ι := Equiv.sumCompl p with he
      haveI huT : Unique {i // ¬ p i} :=
        { default := ⟨j, by simp [hp]⟩
          uniq := fun x => Subtype.ext (by have h := x.2; simp only [hp, not_not] at h; exact h) }
      set M : Matrix ({i // p i} ⊕ {i // ¬ p i}) _ R := A.submatrix e e with hM
      have hMsymm : M.IsSymm := hA.submatrix e
      set A' := M.toBlocks₁₁ with hA'
      set B := M.toBlocks₁₂ with hB
      set D := M.toBlocks₂₂ with hD
      have hCB : M.toBlocks₂₁ = Bᵀ := by
        ext i j
        show M (Sum.inr i) (Sum.inl j) = M (Sum.inl j) (Sum.inr i)
        exact hMsymm.apply (Sum.inl j) (Sum.inr i)
      have hMblock : M = fromBlocks A' B Bᵀ D := by rw [← hCB]; exact (fromBlocks_toBlocks M).symm
      have hA'symm : A'.IsSymm := by rw [hA']; exact hMsymm.submatrix Sum.inl
      have hA'minor : ∀ s : Finset {i // p i},
          0 < (A'.submatrix (Subtype.val : s → _) Subtype.val).det := by
        intro s
        rw [hA', hM]
        exact minor_submatrix_pos hpos
          (⇑e ∘ (Sum.inl : {i // p i} → {i // p i} ⊕ {i // ¬ p i}) ∘
            (Subtype.val : s → {i // p i}))
          (e.injective.comp (Sum.inl_injective.comp Subtype.val_injective))
      have hA'det : 0 < A'.det := by
        have := minor_submatrix_pos hA'minor id Function.injective_id
        rwa [submatrix_id_id] at this
      haveI : Invertible A' := invertibleOfIsUnitDet A' hA'det.ne'.isUnit
      have hcardA' : Fintype.card {i // p i} < n := by
        rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hp])
      have hA'psd : A'.IsPSDForm := IH _ hcardA' _ A' hA'symm hA'minor rfl
      have hdetM : M.det = A.det := by rw [hM, det_submatrix_equiv_self]
      have hdetA : 0 < A.det := by
        have := minor_submatrix_pos hpos id Function.injective_id; rwa [submatrix_id_id] at this
      have hSchurdet : 0 < (D - Bᵀ * A'⁻¹ * B).det := by
        have hfb : A.det = A'.det * (D - Bᵀ * A'⁻¹ * B).det := by
          rw [← hdetM, hMblock, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
        rw [hfb] at hdetA
        exact (mul_pos_iff_of_pos_left hA'det).1 hdetA
      have hMpsd : M.IsPSDForm := by
        rw [hMblock]
        exact isPSDForm_fromBlocks_of_schur hA'symm hA'det.ne'.isUnit (fun y => hA'psd.2 y) B
          (by rw [hD]; exact hMsymm.submatrix Sum.inr)
          (fun t => form_nonneg_of_unique hSchurdet.le t)
      rw [hM] at hMpsd
      exact (isPSDForm_submatrix_iff e).1 hMpsd

end Matrix
