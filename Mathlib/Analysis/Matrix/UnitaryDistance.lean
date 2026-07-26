/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Matrix.NormComparison
public import Mathlib.Analysis.Normed.Ring.Telescope

/-!
# Distance between matrices up to a global phase, and the unitary group as a normed group

Two matrices that differ by a global phase `e ^ (i φ)` represent the same physical operation, so
the natural measure of how well `M` implements a target `U` is the *phase-invariant distance*
`min over ‖c‖ = 1 of ‖M - c • U‖_F`.  This file computes that minimum in closed form: it is
attained at `c = tr(Uᴴ M) / ‖tr(Uᴴ M)‖`, and its square equals
`‖M‖_F² + ‖U‖_F² - 2 ‖tr(Uᴴ M)‖`.

For unitary `M` and `U` this rewrites in terms of the *fidelity* `‖tr(Uᴴ M)‖² / n²`, giving the
standard dictionary between distance and fidelity.

The file also puts a `NormedGroup` structure on `Matrix.unitaryGroup n 𝕜`, with
`‖U‖ = ‖U - 1‖₂`, whose induced metric is the restriction of the spectral metric, and derives
the telescoping error bound for a cascade of unitary stages.

## Main definitions

* `Matrix.toEuclidean`: a matrix viewed as a vector of `EuclideanSpace 𝕜 (m × n)`.  This
  identifies the Frobenius norm with a Euclidean norm and `tr(Aᴴ B)` with an inner product, so
  that the inner product space API applies.
* `Matrix.phaseDist`: the phase-invariant Frobenius distance.
* `Matrix.fidelity`: `‖tr(Uᴴ M)‖ ^ 2 / n ^ 2`.
* `Matrix.UnitaryGroup.normedGroup`: the normed group structure on `Matrix.unitaryGroup n 𝕜`,
  a scoped instance in `Matrix.Norms.L2Operator`.

## Main statements

* `Matrix.norm_trace_conjTranspose_mul_le`: Cauchy–Schwarz, `‖tr(Aᴴ B)‖ ≤ ‖A‖_F ‖B‖_F`.
* `Matrix.frobeniusNorm_sub_smul_sq`: the expansion of `‖M - c • U‖_F ^ 2`.
* `Matrix.isLeast_frobeniusNorm_sub_smul_sq`: the phase-invariant distance is a minimum, not
  just an infimum, and its value is `‖M‖_F² + ‖U‖_F² - 2 ‖tr(Uᴴ M)‖`.
* `Matrix.phaseDist_sq_eq`: for unitary `M` and `U`, `d² = 2n (1 - √F)`.
* `Matrix.l2OpNorm_prod_sub_prod_le`: error propagation through a cascade of unitary stages.

## Tags

matrix, unitary, fidelity, global phase, Frobenius norm
-/

@[expose] public section

open Finset WithLp RCLike
open scoped InnerProductSpace

namespace Matrix

/-! ### Matrices as Euclidean vectors -/

section Def

variable {𝕜 m n : Type*}

/-- A matrix viewed as a vector in `EuclideanSpace 𝕜 (m × n)`.

This identification carries the Frobenius norm to the Euclidean norm
(`Matrix.norm_toEuclidean`) and the trace form `tr(Aᴴ B)` to the inner product
(`Matrix.inner_toEuclidean`), which makes the whole inner product space API available for the
Frobenius norm. -/
def toEuclidean (A : Matrix m n 𝕜) : EuclideanSpace 𝕜 (m × n) :=
  toLp 2 fun p => A p.1 p.2

@[simp]
theorem ofLp_toEuclidean (A : Matrix m n 𝕜) (p : m × n) : ofLp A.toEuclidean p = A p.1 p.2 := rfl

@[simp]
theorem toEuclidean_apply (A : Matrix m n 𝕜) (p : m × n) : A.toEuclidean p = A p.1 p.2 := rfl

@[simp]
theorem toEuclidean_smul {R : Type*} [SMul R 𝕜] (c : R) (A : Matrix m n 𝕜) :
    (c • A).toEuclidean = c • A.toEuclidean := rfl

end Def

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

@[simp]
theorem toEuclidean_sub (A B : Matrix m n 𝕜) :
    (A - B).toEuclidean = A.toEuclidean - B.toEuclidean := rfl

theorem norm_toEuclidean (A : Matrix m n 𝕜) : ‖A.toEuclidean‖ = A.frobeniusNorm := by
  rw [EuclideanSpace.norm_eq, frobeniusNorm, Fintype.sum_prod_type]
  rfl

theorem inner_toEuclidean (A B : Matrix m n 𝕜) :
    ⟪A.toEuclidean, B.toEuclidean⟫_𝕜 = Matrix.trace (Aᴴ * B) := by
  have hR : Matrix.trace (Aᴴ * B) = ∑ j, ∑ i, (starRingEnd 𝕜) (A i j) * B i j := by
    simp only [Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, ← starRingEnd_apply]
  rw [hR, PiLp.inner_apply]
  simp only [RCLike.inner_apply, ofLp_toEuclidean, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Cauchy–Schwarz for the Frobenius inner product.** -/
theorem norm_trace_conjTranspose_mul_le (A B : Matrix m n 𝕜) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ A.frobeniusNorm * B.frobeniusNorm := by
  rw [← inner_toEuclidean, ← norm_toEuclidean, ← norm_toEuclidean]
  exact norm_inner_le_norm _ _

/-! ### Distance up to a global phase -/

variable {c : 𝕜} {M U : Matrix m n 𝕜}

/-- Expansion of the squared Frobenius distance between `M` and a phase-rotated `U`. -/
theorem frobeniusNorm_sub_smul_sq (hc : ‖c‖ = 1) (M U : Matrix m n 𝕜) :
    (M - c • U).frobeniusNorm ^ 2
      = M.frobeniusNorm ^ 2 + U.frobeniusNorm ^ 2
        - 2 * re ((starRingEnd 𝕜) c * Matrix.trace (Uᴴ * M)) := by
  rw [← norm_toEuclidean, ← norm_toEuclidean M, ← norm_toEuclidean U, toEuclidean_sub,
    toEuclidean_smul, norm_sub_sq (𝕜 := 𝕜), inner_smul_right, norm_smul, hc, one_mul,
    inner_toEuclidean]
  have h : (starRingEnd 𝕜) (Matrix.trace (Mᴴ * U)) = Matrix.trace (Uᴴ * M) := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose]
  have h2 : re (c * Matrix.trace (Mᴴ * U)) = re ((starRingEnd 𝕜) c * Matrix.trace (Uᴴ * M)) := by
    rw [← h, ← map_mul, RCLike.conj_re]
  rw [h2]
  ring

/-- Any global phase leaves the distance at least the phase-invariant value. -/
theorem le_frobeniusNorm_sub_smul_sq (hc : ‖c‖ = 1) (M U : Matrix m n 𝕜) :
    M.frobeniusNorm ^ 2 + U.frobeniusNorm ^ 2 - 2 * ‖Matrix.trace (Uᴴ * M)‖
      ≤ (M - c • U).frobeniusNorm ^ 2 := by
  rw [frobeniusNorm_sub_smul_sq hc]
  have : re ((starRingEnd 𝕜) c * Matrix.trace (Uᴴ * M)) ≤ ‖Matrix.trace (Uᴴ * M)‖ := by
    refine (RCLike.re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj, hc, one_mul]
  linarith

/-- The optimal global phase is the argument of `tr(Uᴴ M)`; at that phase the bound of
`Matrix.le_frobeniusNorm_sub_smul_sq` is attained. -/
theorem frobeniusNorm_sub_smul_sq_of_trace_ne_zero (M U : Matrix m n 𝕜)
    (ht : Matrix.trace (Uᴴ * M) ≠ 0) :
    (M - ((‖Matrix.trace (Uᴴ * M)‖ : 𝕜)⁻¹ * Matrix.trace (Uᴴ * M)) • U).frobeniusNorm ^ 2
      = M.frobeniusNorm ^ 2 + U.frobeniusNorm ^ 2 - 2 * ‖Matrix.trace (Uᴴ * M)‖ := by
  set t := Matrix.trace (Uᴴ * M) with htdef
  have hn : (‖t‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr ht
  have hnk : ((‖t‖ : 𝕜)) ≠ 0 := by
    simpa using (RCLike.ofReal_ne_zero (K := 𝕜)).mpr hn
  have hc : ‖(‖t‖ : 𝕜)⁻¹ * t‖ = 1 := by
    rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg t),
      inv_mul_cancel₀ hn]
  rw [frobeniusNorm_sub_smul_sq hc]
  congr 1
  have hval : (starRingEnd 𝕜) ((‖t‖ : 𝕜)⁻¹ * t) * t = ((‖t‖ : ℝ) : 𝕜) := by
    rw [map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul, sq]
    field_simp
  rw [hval, RCLike.ofReal_re]

/-- **The phase-invariant Frobenius distance is a minimum.** -/
theorem isLeast_frobeniusNorm_sub_smul_sq (M U : Matrix m n 𝕜)
    (ht : Matrix.trace (Uᴴ * M) ≠ 0) :
    IsLeast {r : ℝ | ∃ c : 𝕜, ‖c‖ = 1 ∧ (M - c • U).frobeniusNorm ^ 2 = r}
      (M.frobeniusNorm ^ 2 + U.frobeniusNorm ^ 2 - 2 * ‖Matrix.trace (Uᴴ * M)‖) := by
  set t := Matrix.trace (Uᴴ * M) with htdef
  have hn : (‖t‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr ht
  refine ⟨⟨(‖t‖ : 𝕜)⁻¹ * t, ?_, frobeniusNorm_sub_smul_sq_of_trace_ne_zero M U ht⟩, ?_⟩
  · rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg t),
      inv_mul_cancel₀ hn]
  · rintro r ⟨c, hc, rfl⟩
    exact le_frobeniusNorm_sub_smul_sq hc M U

/-- The distance between `M` and `U` after optimizing over the global phase. -/
noncomputable def phaseDist (M U : Matrix m n 𝕜) : ℝ :=
  √(M.frobeniusNorm ^ 2 + U.frobeniusNorm ^ 2 - 2 * ‖Matrix.trace (Uᴴ * M)‖)

theorem phaseDist_nonneg (M U : Matrix m n 𝕜) : 0 ≤ M.phaseDist U := Real.sqrt_nonneg _

theorem phaseDist_sq (M U : Matrix m n 𝕜) :
    M.phaseDist U ^ 2
      = M.frobeniusNorm ^ 2 + U.frobeniusNorm ^ 2 - 2 * ‖Matrix.trace (Uᴴ * M)‖ := by
  refine Real.sq_sqrt ?_
  have h := norm_trace_conjTranspose_mul_le U M
  nlinarith [sq_nonneg (M.frobeniusNorm - U.frobeniusNorm), frobeniusNorm_nonneg M,
    frobeniusNorm_nonneg U]

theorem phaseDist_le_frobeniusNorm_sub_smul (hc : ‖c‖ = 1) (M U : Matrix m n 𝕜) :
    M.phaseDist U ≤ (M - c • U).frobeniusNorm := by
  rw [phaseDist, show (M - c • U).frobeniusNorm = √((M - c • U).frobeniusNorm ^ 2) from
    (Real.sqrt_sq (frobeniusNorm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (le_frobeniusNorm_sub_smul_sq hc M U)

/-! ### Fidelity -/

section Fidelity

variable [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- The squared Frobenius norm of a unitary matrix is the dimension. -/
theorem frobeniusNorm_sq_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ Matrix.unitaryGroup n 𝕜) : U.frobeniusNorm ^ 2 = Fintype.card n := by
  have h : Matrix.trace (Uᴴ * U) = ((Fintype.card n : ℝ) : 𝕜) := by
    rw [conjTranspose_mul_self_of_mem_unitaryGroup hU, Matrix.trace_one]
    norm_cast
  rw [trace_conjTranspose_mul_self, ← frobeniusNorm_sq, RCLike.ofReal_inj] at h
  exact h

/-- The fidelity of `M` with respect to the target `U`, normalized so that `fidelity U U = 1`
for `U` unitary of size `n`. -/
noncomputable def fidelity (U M : Matrix n n 𝕜) : ℝ :=
  ‖Matrix.trace (Uᴴ * M)‖ ^ 2 / (Fintype.card n : ℝ) ^ 2

omit [DecidableEq n] in
theorem fidelity_nonneg (U M : Matrix n n 𝕜) : 0 ≤ fidelity U M := by
  unfold fidelity; positivity

variable {U M : Matrix n n 𝕜}

theorem fidelity_le_one (hU : U ∈ Matrix.unitaryGroup n 𝕜) (hM : M ∈ Matrix.unitaryGroup n 𝕜) :
    fidelity U M ≤ 1 := by
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hcs := norm_trace_conjTranspose_mul_le U M
  have hsq : ‖Matrix.trace (Uᴴ * M)‖ ^ 2 ≤ (Fintype.card n : ℝ) ^ 2 :=
    calc ‖Matrix.trace (Uᴴ * M)‖ ^ 2 ≤ (U.frobeniusNorm * M.frobeniusNorm) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcs 2
      _ = (Fintype.card n : ℝ) ^ 2 := by
          rw [mul_pow, frobeniusNorm_sq_of_mem_unitaryGroup hU,
            frobeniusNorm_sq_of_mem_unitaryGroup hM, sq]
  rw [fidelity, div_le_one (by positivity)]
  exact hsq

/-- **Distance–fidelity dictionary.**  For unitary `M` and `U` of size `n`, the squared
phase-invariant distance is `2 n (1 - √F)`. -/
theorem phaseDist_sq_eq (hU : U ∈ Matrix.unitaryGroup n 𝕜) (hM : M ∈ Matrix.unitaryGroup n 𝕜) :
    M.phaseDist U ^ 2 = 2 * (Fintype.card n : ℝ) * (1 - √(fidelity U M)) := by
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsqrt : √(fidelity U M) = ‖Matrix.trace (Uᴴ * M)‖ / (Fintype.card n : ℝ) := by
    rw [fidelity, ← div_pow, Real.sqrt_sq (by positivity)]
  rw [phaseDist_sq, frobeniusNorm_sq_of_mem_unitaryGroup hU,
    frobeniusNorm_sq_of_mem_unitaryGroup hM, hsqrt]
  field_simp
  ring

end Fidelity

end Matrix

/-! ### The unitary group as a normed group -/

namespace Matrix.UnitaryGroup

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator

/-- The unitary group of `n × n` matrices, as a normed group for the distance
`dist U V = ‖U - V‖₂` inherited from the spectral norm.  The corresponding group norm is
`‖U‖ = ‖U - 1‖₂`.

This is a scoped instance in `Matrix.Norms.L2Operator`, since it depends on the choice of the
spectral norm on `Matrix n n 𝕜`. -/
noncomputable def normedGroup : NormedGroup (Matrix.unitaryGroup n 𝕜) :=
  { (inferInstance : MetricSpace (Matrix.unitaryGroup n 𝕜)),
    (inferInstance : Group (Matrix.unitaryGroup n 𝕜)) with
    norm := fun U => ‖(U : Matrix n n 𝕜) - 1‖
    dist_eq := fun U V => by
      have hV : (V : Matrix n n 𝕜) * (V : Matrix n n 𝕜)ᴴ = 1 :=
        Matrix.mul_conjTranspose_self_of_mem_unitaryGroup V.2
      have hcoe : ((U / V : Matrix.unitaryGroup n 𝕜) : Matrix n n 𝕜)
          = (U : Matrix n n 𝕜) * (V : Matrix n n 𝕜)ᴴ := by
        rw [div_eq_mul_inv, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star,
          Matrix.star_eq_conjTranspose]
      have hstar : (V : Matrix n n 𝕜)ᴴ ∈ Matrix.unitaryGroup n 𝕜 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem V.2
      rw [Subtype.dist_eq, hcoe, dist_eq_norm,
        show (U : Matrix n n 𝕜) * (V : Matrix n n 𝕜)ᴴ - 1
            = ((U : Matrix n n 𝕜) - V) * (V : Matrix n n 𝕜)ᴴ by rw [Matrix.sub_mul, hV],
        ← Matrix.l2OpNorm_eq_norm, ← Matrix.l2OpNorm_eq_norm,
        Matrix.l2OpNorm_mul_of_mem_unitaryGroup' hstar] }

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.UnitaryGroup.normedGroup

theorem norm_def (U : Matrix.unitaryGroup n 𝕜) : ‖U‖ = ‖(U : Matrix n n 𝕜) - 1‖ := rfl

omit [Nonempty n] in
theorem dist_eq_norm_sub (U V : Matrix.unitaryGroup n 𝕜) :
    dist U V = ‖(U : Matrix n n 𝕜) - (V : Matrix n n 𝕜)‖ := by
  rw [Subtype.dist_eq, dist_eq_norm]

end Matrix.UnitaryGroup

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator in
/-- **Error propagation through a cascade of unitary stages.**  If a physical stage `g i`
implements the intended unitary `f i` to within `εᵢ` in spectral norm, the whole cascade
implements the intended product to within `∑ εᵢ`.

This is the noncommutative analogue of `dist_prod_prod_le`, which is unavailable here because
`Matrix n n 𝕜` is not commutative. -/
theorem l2OpNorm_prod_sub_prod_le {k : ℕ} (f g : Fin k → Matrix n n 𝕜)
    (hf : ∀ i, f i ∈ Matrix.unitaryGroup n 𝕜) (hg : ∀ i, g i ∈ Matrix.unitaryGroup n 𝕜) :
    ((List.ofFn f).prod - (List.ofFn g).prod).l2OpNorm ≤ ∑ i, (f i - g i).l2OpNorm := by
  simp only [l2OpNorm_eq_norm]
  exact norm_prod_ofFn_sub_prod_ofFn_le f g
    (fun i => (CStarRing.norm_of_mem_unitary (hf i)).le)
    (fun i => (CStarRing.norm_of_mem_unitary (hg i)).le)

end Matrix
