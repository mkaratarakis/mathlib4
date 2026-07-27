/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Photonics.Matrix.NormComparison

/-!
# A posteriori eigenvalue bounds from a residual

If `A` is Hermitian and a nonzero vector `x` satisfies `‖A x - μ x‖ ≤ ε ‖x‖`, then `μ` is within
`ε` of an actual eigenvalue of `A`.  This is the standard *a posteriori* bound behind the
Rayleigh–Ritz procedure: an approximate eigenpair produced by any means whatsoever — a numerical
eigensolver, a guess, a machine learning model — certifies its own accuracy, because the residual
`A x - μ x` is directly computable from `A`, `x` and `μ`.

The converse direction, that a small residual is *achievable*, is not asserted; the point is that
the hypothesis is checkable and the conclusion is a genuine statement about the spectrum.

## Main statements

* `Matrix.IsHermitian.exists_eigenvalue_near`: the bound, in terms of Euclidean norms.
* `Matrix.IsHermitian.exists_eigenvalue_near_of_sum`: the same, with both sides written as sums
  of squared moduli of entries, which is the form that can be discharged by direct computation.
* `Matrix.IsHermitian.exists_mem_spectrum_near`: the conclusion phrased for `spectrum ℝ A`.

## Tags

Hermitian matrix, eigenvalue, residual, Rayleigh quotient, a posteriori bound
-/

@[expose] public section

open Finset WithLp Unitary

namespace Matrix.IsHermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **A posteriori eigenvalue bound.**  If `x ≠ 0` and the residual `A x - μ x` has Euclidean
norm at most `ε ‖x‖`, then some eigenvalue of the Hermitian matrix `A` lies within `ε` of `μ`. -/
theorem exists_eigenvalue_near {A : Matrix n n 𝕜} (hA : A.IsHermitian) {μ ε : ℝ}
    {x : EuclideanSpace 𝕜 n} (hx : x ≠ 0)
    (h : ‖(toLp 2 (A *ᵥ ofLp x - (μ : 𝕜) • ofLp x) : EuclideanSpace 𝕜 n)‖ ≤ ε * ‖x‖) :
    ∃ i, |hA.eigenvalues i - μ| ≤ ε := by
  haveI : Nonempty n := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hx (Subsingleton.elim x 0)
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hU : U ∈ Matrix.unitaryGroup n 𝕜 := hA.eigenvectorUnitary.2
  have hUs : Uᴴ ∈ Matrix.unitaryGroup n 𝕜 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hU
  set d : n → 𝕜 := fun i => ((hA.eigenvalues i - μ : ℝ) : 𝕜) with hd
  -- `A` is unitarily diagonal, hence so is the shifted matrix `A - μ`.
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hdiag : diagonal d
      = diagonal (RCLike.ofReal ∘ hA.eigenvalues) - (μ : 𝕜) • (1 : Matrix n n 𝕜) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [hd, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
        Algebra.algebraMap_eq_smul_one, sub_smul]
    · simp [hd, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hshift : A - (μ : 𝕜) • (1 : Matrix n n 𝕜) = U * diagonal d * Uᴴ :=
    calc A - (μ : 𝕜) • (1 : Matrix n n 𝕜)
        = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ
            - (μ : 𝕜) • (1 : Matrix n n 𝕜) := by rw [← hspec]
      _ = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ
            - U * ((μ : 𝕜) • (1 : Matrix n n 𝕜)) * Uᴴ := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
            mul_conjTranspose_self_of_mem_unitaryGroup hU]
      _ = U * (diagonal (RCLike.ofReal ∘ hA.eigenvalues) - (μ : 𝕜) • 1) * Uᴴ := by
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      _ = U * diagonal d * Uᴴ := by rw [hdiag]
  have hres : A *ᵥ ofLp x - (μ : 𝕜) • ofLp x = U *ᵥ (diagonal d *ᵥ (Uᴴ *ᵥ ofLp x)) := by
    rw [mulVec_mulVec, mulVec_mulVec, ← hshift, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  -- Pick an eigenvalue closest to `μ`.
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (univ : Finset n)
    (fun i => |hA.eigenvalues i - μ|) Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  set c : ℝ := |hA.eigenvalues i₀ - μ| with hc
  have hc₀ : 0 ≤ c := abs_nonneg _
  have hcd : ∀ i, c ≤ ‖d i‖ := fun i => by
    have hdi : d i = ((hA.eigenvalues i - μ : ℝ) : 𝕜) := rfl
    rw [hdi, RCLike.norm_ofReal]
    exact hi₀ i (mem_univ i)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have key : c * ‖x‖ ≤ ‖(toLp 2 (A *ᵥ ofLp x - (μ : 𝕜) • ofLp x) : EuclideanSpace 𝕜 n)‖ := by
    rw [hres, norm_mulVec_of_mem_unitaryGroup hU
      (toLp 2 (diagonal d *ᵥ (Uᴴ *ᵥ ofLp x)) : EuclideanSpace 𝕜 n)]
    have e := mul_norm_le_norm_mulVec_diagonal hc₀ hcd
      (toLp 2 (Uᴴ *ᵥ ofLp x) : EuclideanSpace 𝕜 n)
    rwa [WithLp.ofLp_toLp, norm_mulVec_of_mem_unitaryGroup hUs x] at e
  exact le_of_mul_le_mul_right (key.trans h) hxpos

/-- **A posteriori eigenvalue bound**, in a form checkable by direct computation on the entries:
both sides are sums of squared moduli. -/
theorem exists_eigenvalue_near_of_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) {μ ε : ℝ}
    (hε : 0 ≤ ε) {v : n → 𝕜} (hv : v ≠ 0)
    (h : ∑ i, ‖(A *ᵥ v - (μ : 𝕜) • v) i‖ ^ 2 ≤ ε ^ 2 * ∑ i, ‖v i‖ ^ 2) :
    ∃ i, |hA.eigenvalues i - μ| ≤ ε := by
  have hsq : ∀ w : n → 𝕜, ‖(toLp 2 w : EuclideanSpace 𝕜 n)‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := fun w => by
    simpa using EuclideanSpace.norm_sq_eq (toLp 2 w)
  refine hA.exists_eigenvalue_near (x := toLp 2 v) (fun hcon => hv ?_) ?_
  · simpa using congrArg ofLp hcon
  · refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [WithLp.ofLp_toLp, mul_pow, hsq, hsq]
    exact h

/-- The conclusion of `Matrix.IsHermitian.exists_eigenvalue_near`, phrased for the real
spectrum. -/
theorem exists_mem_spectrum_near {A : Matrix n n 𝕜} (hA : A.IsHermitian) {μ ε : ℝ}
    {x : EuclideanSpace 𝕜 n} (hx : x ≠ 0)
    (h : ‖(toLp 2 (A *ᵥ ofLp x - (μ : 𝕜) • ofLp x) : EuclideanSpace 𝕜 n)‖ ≤ ε * ‖x‖) :
    ∃ lam ∈ spectrum ℝ A, |lam - μ| ≤ ε := by
  obtain ⟨i, hi⟩ := hA.exists_eigenvalue_near hx h
  exact ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i, hi⟩

end Matrix.IsHermitian
