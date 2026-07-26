/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Comparison of matrix norms

Mathlib equips `Matrix m n α` with several different norms, each as a *scoped* instance in its
own namespace (`Matrix.Norms.Elementwise`, `Matrix.Norms.Operator`, `Matrix.Norms.Frobenius`,
`Matrix.Norms.L2Operator`), because there is no canonical choice.  A consequence is that no two
of them can be in scope at the same time, so a statement such as `‖A‖₂ ≤ ‖A‖_F` cannot be
written directly.

This file works around that by introducing the two norms we wish to compare as plain
`ℝ`-valued functions:

* `Matrix.frobeniusNorm A = √(∑ i, ∑ j, ‖A i j‖ ^ 2)`;
* `Matrix.l2OpNorm A`, the operator norm of `A` acting between Euclidean spaces (the spectral
  norm).

Each agrees, up to `rfl`, with the corresponding scoped instance (`Matrix.frobeniusNorm_eq_norm`,
`Matrix.l2OpNorm_eq_norm`), so results proved here transfer to either scope.  The `ℓ¹` and `ℓ∞`
operator norms enter only through the explicit row and column sums `∑ j, ‖A i j‖` and
`∑ i, ‖A i j‖`, which is both more general and more directly usable in numerical work than the
corresponding suprema.

## Main statements

* `Matrix.l2OpNorm_le_frobeniusNorm`: `‖A‖₂ ≤ ‖A‖_F`.
* `Matrix.l2OpNorm_le_sqrt_mul`: the **Schur test** `‖A‖₂ ≤ √(‖A‖₁ ‖A‖_∞)`, stated with
  explicit bounds on the row and column sums.  Both bounds are computable from the entries
  without any spectral information, which makes this the estimate of choice for rigorous
  numerics.
* `Matrix.norm_entry_le_l2OpNorm`: `‖A i j‖ ≤ ‖A‖₂`.
* `Matrix.frobeniusNorm_le_sqrt_card_mul_l2OpNorm`: `‖A‖_F ≤ √(card n) ‖A‖₂`.
* `Matrix.l2OpNorm_le_sqrt_card_mul`: `‖A‖₂ ≤ √(card m * card n) · max_{i,j} ‖A i j‖`.
* `Matrix.le_l2OpNorm_of_mulVec`: the power-iteration lower bound `‖A *ᵥ v‖ / ‖v‖ ≤ ‖A‖₂`.
* `Matrix.frobeniusNorm_mul_of_mem_unitaryGroup`, `Matrix.l2OpNorm_mul_of_mem_unitaryGroup` and
  their right-handed counterparts: both norms are unitarily invariant.

## Tags

matrix norm, spectral norm, Frobenius norm, Schur test, unitary invariance
-/

@[expose] public section

open Finset WithLp

namespace Matrix

variable {𝕜 α m n : Type*}

/-! ### The Frobenius norm as a plain function -/

section Frobenius

variable [Fintype m] [Fintype n] [SeminormedAddCommGroup α]

/-- The Frobenius (Hilbert–Schmidt) norm `√(∑ i, ∑ j, ‖A i j‖ ^ 2)` of a matrix, as a plain
function.

This is the norm underlying the scoped instances of `Matrix.Norms.Frobenius`, see
`Matrix.frobeniusNorm_eq_norm`.  It is provided as a bare function so that it can be compared
with the other matrix norms, which are mutually incompatible scoped instances on the same
type. -/
noncomputable def frobeniusNorm (A : Matrix m n α) : ℝ := √(∑ i, ∑ j, ‖A i j‖ ^ 2)

theorem frobeniusNorm_nonneg (A : Matrix m n α) : 0 ≤ A.frobeniusNorm := Real.sqrt_nonneg _

@[simp]
theorem frobeniusNorm_sq (A : Matrix m n α) :
    A.frobeniusNorm ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

open scoped Matrix.Norms.Frobenius in
/-- `Matrix.frobeniusNorm` is the norm of the scoped `Matrix.Norms.Frobenius` instances. -/
theorem frobeniusNorm_eq_norm (A : Matrix m n α) : A.frobeniusNorm = ‖A‖ := by
  rw [frobenius_norm_def, frobeniusNorm, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem frobeniusNorm_transpose (A : Matrix m n α) : Aᵀ.frobeniusNorm = A.frobeniusNorm := by
  simp only [frobeniusNorm, transpose_apply]
  rw [Finset.sum_comm]

/-- Every entry of a matrix is bounded by its Frobenius norm. -/
theorem norm_entry_le_frobeniusNorm (A : Matrix m n α) (i : m) (j : n) :
    ‖A i j‖ ≤ A.frobeniusNorm := by
  rw [frobeniusNorm, Real.le_sqrt (norm_nonneg _) (by positivity)]
  calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (mem_univ i)

/-- The Frobenius norm is controlled by the largest entry. -/
theorem frobeniusNorm_le_sqrt_card_mul {A : Matrix m n α} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j, ‖A i j‖ ≤ b) :
    A.frobeniusNorm ≤ √(Fintype.card m * Fintype.card n : ℝ) * b := by
  have hrhs : √((Fintype.card m * Fintype.card n : ℝ) * b ^ 2)
      = √(Fintype.card m * Fintype.card n : ℝ) * b := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb]
  rw [frobeniusNorm, ← hrhs]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : m, ∑ _j : n, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (Fintype.card m * Fintype.card n : ℝ) * b ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Frobenius

/-! ### The `ℓ²` operator norm as a plain function -/

section L2Op

open LinearMap

variable [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- The `ℓ²` operator norm (the spectral norm) of a matrix, as a plain function: the operator
norm of the induced continuous linear map `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m`.

This is the norm underlying the scoped instances of `Matrix.Norms.L2Operator`, see
`Matrix.l2OpNorm_eq_norm`.  It is provided as a bare function so that it can be compared with
the other matrix norms, which are mutually incompatible scoped instances on the same type. -/
noncomputable def l2OpNorm (A : Matrix m n 𝕜) : ℝ :=
  ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖

open scoped Matrix.Norms.L2Operator in
/-- `Matrix.l2OpNorm` is the norm of the scoped `Matrix.Norms.L2Operator` instances. -/
theorem l2OpNorm_eq_norm (A : Matrix m n 𝕜) : A.l2OpNorm = ‖A‖ := rfl

theorem l2OpNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ A.l2OpNorm := norm_nonneg _

/-- The defining property of the `ℓ²` operator norm: it dominates the Euclidean expansion
factor of every vector.  Together with `Matrix.l2OpNorm_le_of_forall` this is the interface
through which the norm should be used. -/
theorem norm_mulVec_le_l2OpNorm_mul (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(toLp 2 (A *ᵥ ofLp x) : EuclideanSpace 𝕜 m)‖ ≤ A.l2OpNorm * ‖x‖ :=
  ContinuousLinearMap.le_opNorm
    ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A) x

theorem l2OpNorm_le_of_forall {A : Matrix m n 𝕜} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : EuclideanSpace 𝕜 n,
      ‖(toLp 2 (A *ᵥ ofLp x) : EuclideanSpace 𝕜 m)‖ ≤ C * ‖x‖) :
    A.l2OpNorm ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h

/-- **Power-iteration lower bound**: any vector certifies a lower bound on the spectral norm.
Combined with `Matrix.l2OpNorm_le_sqrt_mul` this brackets `‖A‖₂` from both sides using only
evaluations of `A`. -/
theorem le_l2OpNorm_of_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(toLp 2 (A *ᵥ ofLp x) : EuclideanSpace 𝕜 m)‖ / ‖x‖ ≤ A.l2OpNorm :=
  div_le_of_le_mul₀ (norm_nonneg _) (l2OpNorm_nonneg A) (norm_mulVec_le_l2OpNorm_mul A x)

private theorem norm_toLp_sq {ι : Type*} [Fintype ι] (w : ι → 𝕜) :
    ‖(toLp 2 w : EuclideanSpace 𝕜 ι)‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
  simpa using EuclideanSpace.norm_sq_eq (toLp 2 w)

omit [DecidableEq n] in
private theorem norm_ofLp_sq (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ j, ‖ofLp x j‖ ^ 2 := by
  simpa using EuclideanSpace.norm_sq_eq x

private theorem norm_toLp_single {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    ‖(toLp 2 (Pi.single j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)‖ = 1 := by
  have h : ‖(toLp 2 (Pi.single j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)‖ ^ 2 = 1 := by
    rw [norm_toLp_sq]
    simp [Pi.single_apply, apply_ite (fun z : 𝕜 => ‖z‖ ^ 2)]
  nlinarith [norm_nonneg ((toLp 2 (Pi.single j (1 : 𝕜))) : EuclideanSpace 𝕜 ι)]

omit [Fintype m] in
private theorem mulVec_ofLp_single (A : Matrix m n 𝕜) (j : n) :
    (A *ᵥ ofLp (toLp 2 (Pi.single j (1 : 𝕜)) : EuclideanSpace 𝕜 n)) = fun i => A i j := by
  funext i
  simp [mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']

omit [Fintype m] [DecidableEq n] in
private theorem norm_mulVec_apply_le (A : Matrix m n 𝕜) (v : n → 𝕜) (i : m) :
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
  rw [mulVec, dotProduct]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _)

/-- Each column of `A` has Euclidean norm at most the spectral norm of `A`. -/
theorem sum_sq_col_le_l2OpNorm_sq (A : Matrix m n 𝕜) (j : n) :
    ∑ i, ‖A i j‖ ^ 2 ≤ A.l2OpNorm ^ 2 := by
  have h := norm_mulVec_le_l2OpNorm_mul A (toLp 2 (Pi.single j (1 : 𝕜)))
  rw [norm_toLp_single, mul_one, mulVec_ofLp_single] at h
  calc ∑ i, ‖A i j‖ ^ 2 = ‖(toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 m)‖ ^ 2 :=
        (norm_toLp_sq _).symm
    _ ≤ A.l2OpNorm ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **The spectral norm is bounded by the Frobenius norm.** -/
theorem l2OpNorm_le_frobeniusNorm (A : Matrix m n 𝕜) : A.l2OpNorm ≤ A.frobeniusNorm := by
  refine l2OpNorm_le_of_forall (frobeniusNorm_nonneg A) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (frobeniusNorm_nonneg A) (norm_nonneg _))).mp ?_
  rw [mul_pow, norm_toLp_sq, norm_ofLp_sq, frobeniusNorm_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(A *ᵥ ofLp x) i‖ ^ 2
      ≤ (∑ j, ‖A i j‖ * ‖ofLp x j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_mulVec_apply_le A _ i) 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖ofLp x j‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Schur test.**  If every row sum of `‖A i j‖` is at most `R` and every column sum is at
most `C`, then the spectral norm of `A` is at most `√(R * C)`.

Both hypotheses are checkable by summing absolute values of entries, with no spectral
information, which makes this the practical way to bound `‖A‖₂` rigorously.  It is sharper than
`Matrix.l2OpNorm_le_frobeniusNorm` for sparse or diagonally dominant matrices. -/
theorem l2OpNorm_le_sqrt_mul (A : Matrix m n 𝕜) {R C : ℝ} (hR₀ : 0 ≤ R) (hC₀ : 0 ≤ C)
    (hR : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hC : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    A.l2OpNorm ≤ √(R * C) := by
  refine l2OpNorm_le_of_forall (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_toLp_sq, norm_ofLp_sq]
  set v : n → 𝕜 := ofLp x with hv
  have step : ∀ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
    intro i
    have cs : (∑ j, ‖A i j‖ * ‖v j‖) ^ 2
        ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
      have key := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset n)
        (fun j => √‖A i j‖) (fun j => √‖A i j‖ * ‖v j‖)
      have e1 : ∀ j : n, √‖A i j‖ * (√‖A i j‖ * ‖v j‖) = ‖A i j‖ * ‖v j‖ := fun j => by
        rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
      have e2 : ∀ j : n, √‖A i j‖ ^ 2 = ‖A i j‖ := fun j => Real.sq_sqrt (norm_nonneg _)
      have e3 : ∀ j : n, (√‖A i j‖ * ‖v j‖) ^ 2 = ‖A i j‖ * ‖v j‖ ^ 2 := fun j => by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      simpa only [e1, e2, e3] using key
    calc ‖(A *ᵥ v) i‖ ^ 2
        ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_mulVec_apply_le A v i) 2
      _ ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := cs
      _ ≤ R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hR i) (Finset.sum_nonneg fun _ _ => by positivity)
  calc ∑ i, ‖(A *ᵥ v) i‖ ^ 2
      ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := Finset.sum_le_sum fun i _ => step i
    _ = R * ∑ j, (∑ i, ‖A i j‖) * ‖v j‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
    _ ≤ R * ∑ j, C * ‖v j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC j) (sq_nonneg _)) hR₀
    _ = R * C * ∑ j, ‖v j‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

/-- Every entry of a matrix is bounded by its spectral norm. -/
theorem norm_entry_le_l2OpNorm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ A.l2OpNorm := by
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ i', ‖A i' j‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ‖A i' j‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) (l2OpNorm_nonneg A)).mp
    (h1.trans (sum_sq_col_le_l2OpNorm_sq A j))

/-- The Frobenius norm is at most `√(card n)` times the spectral norm, where `n` indexes the
columns.  Together with `Matrix.l2OpNorm_le_frobeniusNorm` this shows the two norms are
equivalent, with the sharp constant. -/
theorem frobeniusNorm_le_sqrt_card_mul_l2OpNorm (A : Matrix m n 𝕜) :
    A.frobeniusNorm ≤ √(Fintype.card n : ℝ) * A.l2OpNorm := by
  have hrhs : √(Fintype.card n : ℝ) * A.l2OpNorm = √((Fintype.card n : ℝ) * A.l2OpNorm ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (l2OpNorm_nonneg A)]
  rw [frobeniusNorm, hrhs]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _j : n, A.l2OpNorm ^ 2 :=
        Finset.sum_le_sum fun j _ => sum_sq_col_le_l2OpNorm_sq A j
    _ = (Fintype.card n : ℝ) * A.l2OpNorm ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The spectral norm is controlled by the largest entry. -/
theorem l2OpNorm_le_sqrt_card_mul {A : Matrix m n 𝕜} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j, ‖A i j‖ ≤ b) :
    A.l2OpNorm ≤ √(Fintype.card m * Fintype.card n : ℝ) * b :=
  (l2OpNorm_le_frobeniusNorm A).trans (frobeniusNorm_le_sqrt_card_mul hb h)

end L2Op

/-! ### Unitary invariance -/

section Unitary

variable [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The trace of `Aᴴ * A` is the squared Frobenius norm of `A`. -/
theorem trace_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    Matrix.trace (Aᴴ * A) = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, ← starRingEnd_apply,
    RCLike.conj_mul]
  push_cast
  exact Finset.sum_comm

private theorem frobeniusNorm_eq_of_trace_eq {A B : Matrix m n 𝕜}
    (h : Matrix.trace (Aᴴ * A) = Matrix.trace (Bᴴ * B)) : A.frobeniusNorm = B.frobeniusNorm := by
  rw [trace_conjTranspose_mul_self, trace_conjTranspose_mul_self, RCLike.ofReal_inj] at h
  rw [frobeniusNorm, frobeniusNorm, h]

section Left

variable [DecidableEq m]

theorem conjTranspose_mul_self_of_mem_unitaryGroup {U : Matrix m m 𝕜}
    (hU : U ∈ Matrix.unitaryGroup m 𝕜) : Uᴴ * U = 1 := by
  simpa using Unitary.star_mul_self_of_mem hU

theorem mul_conjTranspose_self_of_mem_unitaryGroup {U : Matrix m m 𝕜}
    (hU : U ∈ Matrix.unitaryGroup m 𝕜) : U * Uᴴ = 1 := by
  simpa using Unitary.mul_star_self_of_mem hU

/-- The Frobenius norm is invariant under multiplication by a unitary matrix on the left. -/
theorem frobeniusNorm_mul_of_mem_unitaryGroup {U : Matrix m m 𝕜}
    (hU : U ∈ Matrix.unitaryGroup m 𝕜) (A : Matrix m n 𝕜) :
    (U * A).frobeniusNorm = A.frobeniusNorm := by
  refine frobeniusNorm_eq_of_trace_eq ?_
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
    conjTranspose_mul_self_of_mem_unitaryGroup hU, Matrix.one_mul]

end Left

section Right

variable [DecidableEq n]

/-- The Frobenius norm is invariant under multiplication by a unitary matrix on the right. -/
theorem frobeniusNorm_mul_of_mem_unitaryGroup' {V : Matrix n n 𝕜}
    (hV : V ∈ Matrix.unitaryGroup n 𝕜) (A : Matrix m n 𝕜) :
    (A * V).frobeniusNorm = A.frobeniusNorm := by
  refine frobeniusNorm_eq_of_trace_eq ?_
  rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm Vᴴ, ← Matrix.mul_assoc,
    Matrix.mul_assoc (Aᴴ * A), mul_conjTranspose_self_of_mem_unitaryGroup hV, Matrix.mul_one]

end Right

section L2Left

variable [DecidableEq m] [DecidableEq n] [Nonempty m]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is invariant under multiplication by a unitary matrix on the left. -/
theorem l2OpNorm_mul_of_mem_unitaryGroup {U : Matrix m m 𝕜}
    (hU : U ∈ Matrix.unitaryGroup m 𝕜) (A : Matrix m n 𝕜) :
    (U * A).l2OpNorm = A.l2OpNorm := by
  have hUn : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
  have hUs : ‖Uᴴ‖ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact CStarRing.norm_of_mem_unitary (Unitary.star_mem hU)
  simp only [l2OpNorm_eq_norm]
  refine le_antisymm ?_ ?_
  · simpa [hUn] using Matrix.l2_opNorm_mul U A
  · calc ‖A‖ = ‖Uᴴ * (U * A)‖ := by
          rw [← Matrix.mul_assoc, conjTranspose_mul_self_of_mem_unitaryGroup hU, Matrix.one_mul]
      _ ≤ ‖Uᴴ‖ * ‖U * A‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖U * A‖ := by rw [hUs, one_mul]

end L2Left

section L2Right

variable [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is invariant under multiplication by a unitary matrix on the right. -/
theorem l2OpNorm_mul_of_mem_unitaryGroup' {V : Matrix n n 𝕜}
    (hV : V ∈ Matrix.unitaryGroup n 𝕜) (A : Matrix m n 𝕜) :
    (A * V).l2OpNorm = A.l2OpNorm := by
  have hVn : ‖V‖ = 1 := CStarRing.norm_of_mem_unitary hV
  have hVs : ‖Vᴴ‖ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact CStarRing.norm_of_mem_unitary (Unitary.star_mem hV)
  simp only [l2OpNorm_eq_norm]
  refine le_antisymm ?_ ?_
  · simpa [hVn] using Matrix.l2_opNorm_mul A V
  · calc ‖A‖ = ‖A * V * Vᴴ‖ := by
          rw [Matrix.mul_assoc, mul_conjTranspose_self_of_mem_unitaryGroup hV, Matrix.mul_one]
      _ ≤ ‖A * V‖ * ‖Vᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖A * V‖ := by rw [hVs, mul_one]

end L2Right

end Unitary

end Matrix
