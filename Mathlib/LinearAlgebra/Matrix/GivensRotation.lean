/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Givens rotations

A Givens rotation (also called a plane rotation, see [horn2013]*Section 2.1) is a matrix which
coincides with the identity except in the four entries lying in two rows and columns `i ≠ j`,
where it is of the form

```
⋱
  c ⋯  s
  ⋮ ⋱  ⋮
 -s̄ ⋯  c̄
       ⋱
```

with `c * star c + s * star s = 1`. Over `ℝ` (with `c = cos θ`, `s = sin θ`) these are the
rotations by an angle `θ` in the `(i, j)`-coordinate plane; over `ℂ` they are the natural
unitary generalization. Multiplying a matrix by a Givens rotation on the left modifies only
rows `i` and `j`, which makes Givens rotations a basic tool to operate on the rows of a matrix
while staying inside the unitary group; they are a unitary analogue of the transvections of
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`.

The definition and the entrywise API are developed over a (possibly noncommutative) star ring;
the statements involving the unitary group and the determinant are over a commutative star
ring. The elimination step and the resulting factorization of unitary matrices as products of
Givens rotations and a diagonal unitary matrix (QR factorization, or, in the physics
literature, the Reck decomposition of an optical interferometer mesh) require square roots, and
are proved over an `RCLike` field in `Mathlib/Analysis/Matrix/GivensRotation.lean`.

## Main definitions and results

* `Matrix.givensRotation i j c s` is the matrix equal to the identity except for the four
  entries `(i, i)`, `(i, j)`, `(j, i)`, `(j, j)`, where it is given by the 2×2 block
  `!![c, s; -star s, star c]`.
* `Matrix.givensRotation_mem_unitaryGroup` : if `c * star c + s * star s = 1` then
  `givensRotation i j c s` is unitary.
* `Matrix.det_givensRotation` : `det (givensRotation i j c s) = c * star c + s * star s`.
  In particular a unitary Givens rotation lies in the special unitary group
  (`Matrix.givensRotation_mem_specialUnitaryGroup`).
* `Matrix.GivensRotationStruct n R` is a structure containing the data of a unitary Givens
  rotation: indices `i, j` with a proof `i ≠ j`, and coefficients `c, s` with a proof of
  `c * star c + s * star s = 1`. It is easier to manipulate than raw matrices in inductive
  arguments, especially through lists.
* `Matrix.mem_unitaryGroup_fin_two_iff_exists_givensRotation` : a `2 × 2` matrix is unitary iff
  it is a diagonal phase times a Givens rotation. This is the standard parameterization of
  `U(2)`.
* `Matrix.diagonal_mul_givensRotation` : diagonal matrices with unitary entries commute past
  Givens rotations, up to a unitary change of the coefficient `c` and a swap of the two
  relevant diagonal entries. Together with its list version
  `Matrix.GivensRotationStruct.exists_diagonal_mul_prod_toMatrix_eq`, this is the rule for
  propagating a phase screen through an interferometer mesh.
* `Matrix.mem_specialUnitaryGroup_fin_two_iff_exists_givensRotation` : a `2 × 2` matrix is
  special unitary iff it is a Givens rotation; `SU(2)` consists exactly of the 2×2 Givens
  rotations. Over `ℝ` this parameterizes `SO(2)`; see
  `Matrix.mem_specialUnitaryGroup_fin_two_iff_exists_angle` in
  `Mathlib/Analysis/Matrix/GivensRotation.lean` for the angle form.

## Tags

rotation, unitary group, elementary matrices, QR
-/

@[expose] public section

namespace Matrix

open Sum

variable {m n p : Type*} [DecidableEq n] [DecidableEq p]

/-! ### Givens rotations over a star ring

The definition, the entrywise description, and the action on rows, columns and vectors make
sense (and are proved here) over a possibly noncommutative star ring, so that they apply, for
instance, to matrices over the quaternions. -/

section Ring

variable {R : Type*} [Ring R] [StarRing R] (i j : n) (c s : R)

/-- The Givens rotation `givensRotation i j c s` is equal to the identity except in rows and
columns `i` and `j`, where it is given (for `i ≠ j`) by the 2×2 block
`!![c, s; -star s, star c]`. When `c * star c + s * star s = 1`, this matrix is unitary, see
`Matrix.givensRotation_mem_unitaryGroup`. -/
def givensRotation : Matrix n n R :=
  1 + single i i (c - 1) + single i j s + single j i (-star s) + single j j (star c - 1)

@[simp]
theorem givensRotation_one_zero : givensRotation i j 1 0 = (1 : Matrix n n R) := by
  simp [givensRotation]

variable {i j}

section Entries

variable {a b : n}

@[simp]
theorem givensRotation_apply_ii (hij : i ≠ j) : givensRotation i j c s i i = c := by
  simp [givensRotation, hij.symm]

@[simp]
theorem givensRotation_apply_ij (hij : i ≠ j) : givensRotation i j c s i j = s := by
  simp [givensRotation, hij, hij.symm]

@[simp]
theorem givensRotation_apply_ji (hij : i ≠ j) : givensRotation i j c s j i = -star s := by
  simp [givensRotation, hij, hij.symm]

@[simp]
theorem givensRotation_apply_jj (hij : i ≠ j) : givensRotation i j c s j j = star c := by
  simp [givensRotation, hij]

/-- Away from rows `i` and `j`, a Givens rotation coincides with the identity matrix. -/
@[simp]
theorem givensRotation_apply_of_ne (ha : a ≠ i) (ha' : a ≠ j) (b : n) :
    givensRotation i j c s a b = (1 : Matrix n n R) a b := by
  simp [givensRotation, ha.symm, ha'.symm]

/-- In row `i`, a Givens rotation vanishes away from columns `i` and `j`. -/
@[simp]
theorem givensRotation_apply_left_of_ne (hb : b ≠ i) (hb' : b ≠ j) :
    givensRotation i j c s i b = 0 := by
  simp [givensRotation, hb.symm, hb'.symm]

/-- In row `j`, a Givens rotation vanishes away from columns `i` and `j`. -/
@[simp]
theorem givensRotation_apply_right_of_ne (hb : b ≠ i) (hb' : b ≠ j) :
    givensRotation i j c s j b = 0 := by
  simp [givensRotation, hb.symm, hb'.symm]

end Entries

/-- The star (conjugate transpose) of a Givens rotation is a Givens rotation. -/
@[simp]
theorem star_givensRotation :
    star (givensRotation i j c s) = givensRotation i j (star c) (-s) := by
  simp only [givensRotation, star_eq_conjTranspose, conjTranspose_add, conjTranspose_one,
    conjTranspose_single, star_sub, star_one, star_star, star_neg, neg_neg]
  abel

section Action

variable [Fintype n] {a b : n}

/-- Multiplying `M` by `givensRotation i j c s` on the left replaces the `i`-th row of `M` with
`c` times the `i`-th row plus `s` times the `j`-th row. -/
@[simp]
theorem givensRotation_mul_apply_left (hij : i ≠ j) (M : Matrix n m R) (b : m) :
    (givensRotation i j c s * M) i b = c * M i b + s * M j b := by
  simp only [givensRotation, Matrix.add_mul, Matrix.one_mul, add_apply, single_mul_apply_same,
    ne_eq, hij, not_false_eq_true, single_mul_apply_of_ne, add_zero, add_left_inj]
  noncomm_ring

/-- Multiplying `M` by `givensRotation i j c s` on the left replaces the `j`-th row of `M` with
`-star s` times the `i`-th row plus `star c` times the `j`-th row. -/
@[simp]
theorem givensRotation_mul_apply_right (hij : i ≠ j) (M : Matrix n m R) (b : m) :
    (givensRotation i j c s * M) j b = -star s * M i b + star c * M j b := by
  simp only [givensRotation, Matrix.add_mul, Matrix.one_mul, add_apply, ne_eq, hij.symm,
    not_false_eq_true, single_mul_apply_of_ne, add_zero, single_mul_apply_same, neg_mul]
  noncomm_ring

/-- Multiplying by a Givens rotation on the left only modifies rows `i` and `j`. -/
@[simp]
theorem givensRotation_mul_apply_of_ne (ha : a ≠ i) (ha' : a ≠ j) (M : Matrix n m R) (b : m) :
    (givensRotation i j c s * M) a b = M a b := by
  simp [givensRotation, Matrix.add_mul, ha, ha']

/-- Multiplying `M` by `givensRotation i j c s` on the right replaces the `i`-th column of `M`
with `c` times the `i`-th column minus `star s` times the `j`-th column. -/
@[simp]
theorem mul_givensRotation_apply_left (hij : i ≠ j) (M : Matrix m n R) (a : m) :
    (M * givensRotation i j c s) a i = M a i * c - M a j * star s := by
  simp only [givensRotation, Matrix.mul_add, Matrix.mul_one, add_apply, mul_single_apply_same,
    ne_eq, hij, not_false_eq_true, mul_single_apply_of_ne, add_zero, mul_neg]
  noncomm_ring

/-- Multiplying `M` by `givensRotation i j c s` on the right replaces the `j`-th column of `M`
with `s` times the `i`-th column plus `star c` times the `j`-th column. -/
@[simp]
theorem mul_givensRotation_apply_right (hij : i ≠ j) (M : Matrix m n R) (a : m) :
    (M * givensRotation i j c s) a j = M a i * s + M a j * star c := by
  simp only [givensRotation, Matrix.mul_add, Matrix.mul_one, add_apply, ne_eq, hij.symm,
    not_false_eq_true, mul_single_apply_of_ne, add_zero, mul_single_apply_same]
  noncomm_ring

/-- Multiplying by a Givens rotation on the right only modifies columns `i` and `j`. -/
@[simp]
theorem mul_givensRotation_apply_of_ne (hb : b ≠ i) (hb' : b ≠ j) (M : Matrix m n R) (a : m) :
    (M * givensRotation i j c s) a b = M a b := by
  simp [givensRotation, Matrix.mul_add, hb, hb']

/-- The action of a Givens rotation on a vector, at the `i`-th coordinate. -/
@[simp]
theorem givensRotation_mulVec_left (hij : i ≠ j) (v : n → R) :
    (givensRotation i j c s).mulVec v i = c * v i + s * v j := by
  simp only [givensRotation, add_mulVec, one_mulVec, single_mulVec, neg_mul, Pi.add_apply,
    Function.update_self, ne_eq, hij, not_false_eq_true, Function.update_of_ne, Pi.zero_apply,
    add_zero, add_left_inj]
  noncomm_ring

/-- The action of a Givens rotation on a vector, at the `j`-th coordinate. -/
@[simp]
theorem givensRotation_mulVec_right (hij : i ≠ j) (v : n → R) :
    (givensRotation i j c s).mulVec v j = -star s * v i + star c * v j := by
  simp only [givensRotation, add_mulVec, one_mulVec, single_mulVec, neg_mul, Pi.add_apply,
    ne_eq, hij.symm, not_false_eq_true, Function.update_of_ne, Pi.zero_apply, add_zero,
    Function.update_self]
  noncomm_ring

/-- The action of a Givens rotation on a vector only modifies the `i`-th and `j`-th
coordinates. -/
@[simp]
theorem givensRotation_mulVec_of_ne (ha : a ≠ i) (ha' : a ≠ j) (v : n → R) :
    (givensRotation i j c s).mulVec v a = v a := by
  simp [givensRotation, add_mulVec, single_mulVec, ha, ha']

end Action

section Blocks

omit [StarRing R] in
/-- A basis matrix supported in the first component of a sum type is a block matrix. -/
theorem single_inl_inl (i j : n) (x : R) :
    (single (inl i) (inl j) x : Matrix (n ⊕ p) (n ⊕ p) R) =
      fromBlocks (single i j x) 0 0 0 := by
  ext (a | a) (b | b) <;> simp [single_apply]

/-- Embedding a Givens rotation along `Sum.inl` produces a block matrix. -/
theorem givensRotation_inl_inl (i j : n) (c s : R) :
    (givensRotation (inl i) (inl j) c s : Matrix (n ⊕ p) (n ⊕ p) R) =
      fromBlocks (givensRotation i j c s) 0 0 1 := by
  rw [givensRotation, givensRotation, ← fromBlocks_one]
  simp only [single_inl_inl, fromBlocks_add, add_zero]

/-- Reindexing a Givens rotation along an equivalence yields a Givens rotation. -/
theorem reindex_givensRotation (e : n ≃ p) (i j : n) (c s : R) :
    reindex e e (givensRotation i j c s) = givensRotation (e i) (e j) c s := by
  simp [givensRotation, reindex_apply, submatrix_add, submatrix_one_equiv,
    submatrix_single_equiv]

end Blocks

end Ring

/-! ### Unitarity and determinant

Over a commutative star ring, Givens rotations in a fixed plane are closed under
multiplication, a Givens rotation with `c * star c + s * star s = 1` is unitary, and its
determinant is `c * star c + s * star s`, so that unitary Givens rotations lie in the special
unitary group. -/

variable {R : Type*} [CommRing R] [StarRing R]

section GivensRotation

variable {i j : n} (c s : R)

/-- Givens rotations in a fixed plane are stable under multiplication; the coefficients multiply
like the corresponding 2×2 blocks. -/
theorem givensRotation_mul_givensRotation [Fintype n] (hij : i ≠ j) (c₁ s₁ c₂ s₂ : R) :
    givensRotation i j c₁ s₁ * givensRotation i j c₂ s₂ =
      givensRotation i j (c₁ * c₂ - s₁ * star s₂) (c₁ * s₂ + s₁ * star c₂) := by
  ext a b
  rcases eq_or_ne a i with rfl | hai
  · rw [givensRotation_mul_apply_left _ _ hij]
    simp only [givensRotation, add_apply, one_apply, single_apply]
    grind [star_mul', star_add, star_sub, star_star]
  rcases eq_or_ne a j with rfl | haj
  · rw [givensRotation_mul_apply_right _ _ hij]
    simp only [givensRotation, add_apply, one_apply, single_apply]
    grind [star_mul', star_add, star_sub, star_star]
  · rw [givensRotation_mul_apply_of_ne _ _ hai haj]
    simp only [givensRotation, add_apply, one_apply, single_apply]
    grind

/-- A Givens rotation with `c * star c + s * star s = 1` is unitary. -/
theorem givensRotation_mem_unitaryGroup [Fintype n] (hij : i ≠ j)
    (h : c * star c + s * star s = 1) : givensRotation i j c s ∈ unitaryGroup n R := by
  rw [mem_unitaryGroup_iff, star_givensRotation, givensRotation_mul_givensRotation hij]
  simp only [star_neg, mul_neg, sub_neg_eq_add, star_star, h, mul_comm s c, neg_add_cancel,
    givensRotation_one_zero]

section Det

variable [Fintype n]

/-- The determinant of a Givens rotation. In particular, Givens rotations with
`c * star c + s * star s = 1` lie in the special unitary group. -/
@[simp]
theorem det_givensRotation (hij : i ≠ j) :
    (givensRotation i j c s).det = c * star c + s * star s := by
  have key : givensRotation i j c s =
      1 + (single i 0 1 + single j 1 1 : Matrix n (Fin 2) R) *
        (single 0 i (c - 1) + single 0 j s + single 1 i (-star s) + single 1 j (star c - 1) :
          Matrix (Fin 2) n R) := by
    simp [givensRotation, Matrix.add_mul, Matrix.mul_add, add_assoc]
  rw [key, det_one_add_mul_comm, det_fin_two]
  simp [Matrix.mul_add, Matrix.add_mul, hij, hij.symm]

/-- A Givens rotation with `c * star c + s * star s = 1` lies in the special unitary group. -/
theorem givensRotation_mem_specialUnitaryGroup (hij : i ≠ j)
    (h : c * star c + s * star s = 1) : givensRotation i j c s ∈ specialUnitaryGroup n R :=
  mem_specialUnitaryGroup_iff.mpr
    ⟨givensRotation_mem_unitaryGroup _ _ hij h, by rw [det_givensRotation _ _ hij, h]⟩

end Det

section Diagonal

variable {d : n → R}

/-- Diagonal matrices with unitary entries commute past Givens rotations, after swapping the
two relevant diagonal entries and multiplying the coefficient `c` by a unitary phase. In the
language of interferometer meshes, this is the rule for propagating a phase screen through a
beam splitter. -/
theorem diagonal_mul_givensRotation [Fintype n] (hij : i ≠ j) (hi : d i ∈ unitary R)
    (hj : d j ∈ unitary R) :
    diagonal d * givensRotation i j c s =
      givensRotation i j (d i * star (d j) * c) s * diagonal (d ∘ Equiv.swap i j) := by
  ext a b
  rw [diagonal_mul, mul_diagonal, Function.comp_apply]
  simp only [givensRotation, add_apply, one_apply, single_apply]
  grind [star_mul', star_star, hi.1, hi.2, hj.1, hj.2]

end Diagonal

end GivensRotation

section UnitaryHelpers

variable [Fintype n] [Fintype p]

/-- Reindexing preserves unitarity. -/
theorem reindexAlgEquiv_mem_unitaryGroup (e : n ≃ p) {U : Matrix n n R}
    (hU : U ∈ unitaryGroup n R) : reindexAlgEquiv R _ e U ∈ unitaryGroup p R := by
  rw [mem_unitaryGroup_iff] at hU ⊢
  rw [reindexAlgEquiv_apply, reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, ← star_eq_conjTranspose, hU, submatrix_one_equiv]

/-- A block diagonal matrix (with respect to a decomposition of the index type as a sum) is
unitary iff both diagonal blocks are unitary. -/
theorem fromBlocks_mem_unitaryGroup_iff {A : Matrix n n R} {D : Matrix p p R} :
    fromBlocks A 0 0 D ∈ unitaryGroup (n ⊕ p) R ↔
      A ∈ unitaryGroup n R ∧ D ∈ unitaryGroup p R := by
  rw [mem_unitaryGroup_iff, ← fromBlocks_one (l := n) (m := p)]
  simp [-fromBlocks_one, mem_unitaryGroup_iff, star_eq_conjTranspose, fromBlocks_conjTranspose,
    fromBlocks_multiply]

end UnitaryHelpers

variable (n R) in
/-- A structure containing all the data defining a unitary Givens rotation: two indices `i ≠ j`
and two coefficients `c`, `s` satisfying `c * star c + s * star s = 1`. This structure is easier
to manipulate than the corresponding matrices, especially in inductive arguments. -/
structure GivensRotationStruct where
  /-- The first index of the plane of rotation. -/
  i : n
  /-- The second index of the plane of rotation. -/
  j : n
  hij : i ≠ j
  /-- The diagonal coefficient (`cos θ` for a real rotation by `θ`). -/
  c : R
  /-- The off-diagonal coefficient (`sin θ` for a real rotation by `θ`). -/
  s : R
  norm_eq : c * star c + s * star s = 1

namespace GivensRotationStruct

variable {i j : n} {c s : R}

/-- Associating to a `GivensRotationStruct` the corresponding matrix. -/
def toMatrix (g : GivensRotationStruct n R) : Matrix n n R :=
  givensRotation g.i g.j g.c g.s

@[simp]
theorem toMatrix_mk (hij : i ≠ j) (h : c * star c + s * star s = 1) :
    (⟨i, j, hij, c, s, h⟩ : GivensRotationStruct n R).toMatrix = givensRotation i j c s :=
  rfl

section Fintype

variable [Fintype n]

theorem toMatrix_mem_unitaryGroup (g : GivensRotationStruct n R) :
    g.toMatrix ∈ unitaryGroup n R :=
  givensRotation_mem_unitaryGroup _ _ g.hij g.norm_eq

@[simp]
protected theorem det (g : GivensRotationStruct n R) : g.toMatrix.det = 1 := by
  rw [toMatrix, det_givensRotation _ _ g.hij, g.norm_eq]

theorem toMatrix_mem_specialUnitaryGroup (g : GivensRotationStruct n R) :
    g.toMatrix ∈ specialUnitaryGroup n R :=
  givensRotation_mem_specialUnitaryGroup _ _ g.hij g.norm_eq

theorem toMatrix_prod_mem_unitaryGroup (L : List (GivensRotationStruct n R)) :
    (L.map toMatrix).prod ∈ unitaryGroup n R :=
  Submonoid.list_prod_mem _ (by simpa using fun g _ => g.toMatrix_mem_unitaryGroup)

/-- The vector action of the matrix of a `GivensRotationStruct` only modifies the coordinates
in the plane of rotation. -/
theorem toMatrix_mulVec_of_ne (g : GivensRotationStruct n R) {a : n} (ha : a ≠ g.i)
    (ha' : a ≠ g.j) (v : n → R) : g.toMatrix.mulVec v a = v a :=
  givensRotation_mulVec_of_ne _ _ ha ha' v

end Fintype

/-- The inverse of a `GivensRotationStruct`, designed so that `g.inv.toMatrix` is the inverse of
`g.toMatrix`. -/
@[simps]
protected def inv (g : GivensRotationStruct n R) : GivensRotationStruct n R where
  i := g.i
  j := g.j
  hij := g.hij
  c := star g.c
  s := -g.s
  norm_eq := by
    simp only [star_star, star_neg, mul_neg, neg_mul, neg_neg]
    linear_combination g.norm_eq

/-- The matrix of the inverse of a `GivensRotationStruct` is the conjugate transpose of its
matrix. -/
theorem toMatrix_inv (g : GivensRotationStruct n R) : g.inv.toMatrix = star g.toMatrix :=
  (star_givensRotation _ _).symm

section Fintype

variable [Fintype n]

theorem inv_mul (g : GivensRotationStruct n R) : g.inv.toMatrix * g.toMatrix = 1 := by
  rw [toMatrix_inv]
  exact mem_unitaryGroup_iff'.mp g.toMatrix_mem_unitaryGroup

theorem mul_inv (g : GivensRotationStruct n R) : g.toMatrix * g.inv.toMatrix = 1 := by
  rw [toMatrix_inv]
  exact mem_unitaryGroup_iff.mp g.toMatrix_mem_unitaryGroup

/-- The product of the matrices of the inverses, in reverse order, is the star of the product
of the matrices. -/
theorem prod_reverse_map_inv_toMatrix (L : List (GivensRotationStruct n R)) :
    (L.reverse.map (toMatrix ∘ GivensRotationStruct.inv)).prod = star (L.map toMatrix).prod := by
  induction L with
  | nil => simp
  | cons g L IH =>
    simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, star_mul, IH,
      Function.comp_apply, toMatrix_inv]

theorem reverse_inv_prod_mul_prod (L : List (GivensRotationStruct n R)) :
    (L.reverse.map (toMatrix ∘ GivensRotationStruct.inv)).prod * (L.map toMatrix).prod = 1 := by
  rw [prod_reverse_map_inv_toMatrix]
  exact mem_unitaryGroup_iff'.mp (toMatrix_prod_mem_unitaryGroup L)

theorem prod_mul_reverse_inv_prod (L : List (GivensRotationStruct n R)) :
    (L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ GivensRotationStruct.inv)).prod = 1 := by
  rw [prod_reverse_map_inv_toMatrix]
  exact mem_unitaryGroup_iff.mp (toMatrix_prod_mem_unitaryGroup L)

end Fintype

/-- Given a `GivensRotationStruct` on `n`, define the corresponding `GivensRotationStruct` on
`n ⊕ p` using the identity on `p`. -/
def sumInl (p : Type*) (g : GivensRotationStruct n R) : GivensRotationStruct (n ⊕ p) R where
  i := inl g.i
  j := inl g.j
  hij := inl_injective.ne g.hij
  c := g.c
  s := g.s
  norm_eq := g.norm_eq

theorem toMatrix_sumInl (g : GivensRotationStruct n R) :
    (g.sumInl p).toMatrix = fromBlocks g.toMatrix 0 0 1 :=
  givensRotation_inl_inl _ _ _ _

@[simp]
theorem sumInl_toMatrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (GivensRotationStruct n R)) (N : Matrix p p R) :
    (L.map (toMatrix ∘ sumInl p)).prod * fromBlocks M 0 0 N =
      fromBlocks ((L.map toMatrix).prod * M) 0 0 N := by
  induction L with
  | nil => simp
  | cons g L IH => simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]

/-- Given a `GivensRotationStruct` on `n` and an equivalence between `n` and `p`, define the
corresponding `GivensRotationStruct` on `p`. -/
def reindexEquiv (e : n ≃ p) (g : GivensRotationStruct n R) : GivensRotationStruct p R where
  i := e g.i
  j := e g.j
  hij := e.injective.ne g.hij
  c := g.c
  s := g.s
  norm_eq := g.norm_eq

variable [Fintype n] [Fintype p]

theorem toMatrix_reindexEquiv (e : n ≃ p) (g : GivensRotationStruct n R) :
    (g.reindexEquiv e).toMatrix = reindexAlgEquiv R _ e g.toMatrix :=
  (reindex_givensRotation e g.i g.j g.c g.s).symm

theorem toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (GivensRotationStruct n R)) :
    (L.map (toMatrix ∘ reindexEquiv e)).prod = reindexAlgEquiv R _ e (L.map toMatrix).prod := by
  rw [map_list_prod, List.map_map]
  simp [Function.comp_def, toMatrix_reindexEquiv]

/-- A diagonal matrix with unitary entries can be moved from the left of a product of Givens
rotations to its right, without changing the planes of the rotations. In the language of
interferometer meshes: a phase screen can be propagated through a mesh of beam splitters,
leaving the mesh geometry unchanged. -/
theorem exists_diagonal_mul_prod_toMatrix_eq (d : n → R) (hd : ∀ k, d k ∈ unitary R)
    (L : List (GivensRotationStruct n R)) :
    ∃ (L' : List (GivensRotationStruct n R)) (d' : n → R),
      (∀ k, d' k ∈ unitary R) ∧
      List.Forall₂ (fun g g' => g.i = g'.i ∧ g.j = g'.j) L L' ∧
      diagonal d * (L.map toMatrix).prod = (L'.map toMatrix).prod * diagonal d' := by
  induction L generalizing d with
  | nil => exact ⟨[], d, hd, List.Forall₂.nil, by simp⟩
  | cons g L IH =>
    obtain ⟨i, j, hij, c, s, hnorm⟩ := g
    obtain ⟨L', d', hd', hL', h⟩ := IH (d ∘ Equiv.swap i j) fun k => hd _
    refine ⟨⟨i, j, hij, d i * star (d j) * c, s, ?_⟩ :: L', d', hd',
      List.Forall₂.cons ⟨rfl, rfl⟩ hL', ?_⟩
    · simp only [star_mul', star_star]
      linear_combination (c * star c * (d j * star (d j))) * (hd i).2 +
        (c * star c) * (hd j).2 + hnorm
    · simp only [List.map_cons, List.prod_cons, toMatrix_mk]
      rw [← Matrix.mul_assoc, diagonal_mul_givensRotation c s hij (hd i) (hd j),
        Matrix.mul_assoc, h, ← Matrix.mul_assoc]

end GivensRotationStruct

/-! ### The parameterizations of `U(2)` and `SU(2)`

A `2 × 2` matrix is unitary iff it is a diagonal phase times a Givens rotation, and special
unitary iff it is a Givens rotation. In other words, the unitary Givens rotations in a fixed
plane are exactly the embedded copies of `SU(2)`. -/

section FinTwo

/-- The parameterization of the unitary group `U(2)`: a `2 × 2` matrix is unitary if and only if
it is the product of a diagonal phase and a Givens rotation. See
`Matrix.of_mem_unitaryGroup_fin_two_iff` for the entrywise version. -/
theorem mem_unitaryGroup_fin_two_iff_exists_givensRotation
    {U : Matrix (Fin 2) (Fin 2) R} :
    U ∈ unitaryGroup (Fin 2) R ↔
      ∃ c s u : R, c * star c + s * star s = 1 ∧ u ∈ unitary R ∧
        U = diagonal ![1, u] * givensRotation 0 1 c s := by
  constructor
  · intro hU
    obtain ⟨e, u, hu, h10, h11⟩ := mem_unitaryGroup_fin_two_iff.mp hU
    refine ⟨U 0 0, U 0 1, u, e, hu, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h10, h11] <;> ring
  · rintro ⟨c, s, u, h, hu, rfl⟩
    exact mul_mem
      (diagonal_mem_unitaryGroup_iff.mpr fun k => by
        fin_cases k
        · simp
        · simpa using hu)
      (givensRotation_mem_unitaryGroup _ _ Fin.zero_ne_one h)

/-- The parameterization of the special unitary group `SU(2)`: a `2 × 2` matrix is special
unitary if and only if it is a Givens rotation. Over `ℝ`, this says that `SO(2)` consists
exactly of the plane rotation matrices. See
`Matrix.of_mem_specialUnitaryGroup_fin_two_iff` for the entrywise version and
`Matrix.mem_specialUnitaryGroup_fin_two_iff_exists_angle` for the angle form over `ℝ`. -/
theorem mem_specialUnitaryGroup_fin_two_iff_exists_givensRotation
    {U : Matrix (Fin 2) (Fin 2) R} :
    U ∈ specialUnitaryGroup (Fin 2) R ↔
      ∃ c s : R, c * star c + s * star s = 1 ∧ U = givensRotation 0 1 c s := by
  rw [mem_specialUnitaryGroup_fin_two_iff]
  constructor
  · rintro ⟨e, h10, h11⟩
    refine ⟨U 0 0, U 0 1, e, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h10, h11]
  · rintro ⟨c, s, h, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [h]

end FinTwo

end Matrix
