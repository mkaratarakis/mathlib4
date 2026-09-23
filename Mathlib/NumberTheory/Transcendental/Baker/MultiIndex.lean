/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.NumberTheory.Transcendental.Baker.AnalyticTsum

/-!
# Power series in several variables are analytic

A power series in several variables `∑ α, z ^ α • c α`, indexed by multi-indices
`α : ι → ℕ`, is a sum of monomials.  Each monomial is a continuous multilinear map
restricted to the diagonal, hence has an explicit one-term formal multilinear series of
norm at most `‖c α‖`; `analyticAt_tsum` then assembles them.

This is the bridge that lets one produce an `AnalyticAt` on a product `ι → 𝕜` from
coefficient bounds alone, which is how the Cauchy integral on a polydisc is shown to be
analytic.  Mathlib had the two ends — that multivariable polynomials are analytic, and
`FormalMultilinearSeries` — but not the passage from a multi-indexed series to either.

This file belongs in `Mathlib/Analysis/Analytic/Constructions.lean`.

## Main statements

* `monomialSeries`: the one-term formal multilinear series of the monomial `z ^ α • c`.
* `hasFPowerSeriesOnBall_monomial`: it is indeed its power series, on any ball.
* `analyticAt_tsum_monomial`: a normally convergent multi-index power series is analytic.
-/

@[expose] public section

open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The slots of the monomial `z ^ α`: one slot for each unit of each exponent. -/
abbrev MonomialSlots (α : ι → ℕ) : Type _ := Σ i : ι, Fin (α i)

/-- The monomial `z ↦ (∏ i, z i ^ α i) • c`, as a continuous multilinear map with one
argument per slot; the slot `⟨i, _⟩` contributes the coordinate `i`. -/
noncomputable def monomialCMM (α : ι → ℕ) (c : F) :
    ContinuousMultilinearMap 𝕜 (fun _ : MonomialSlots α => (ι → 𝕜)) F :=
  ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 (MonomialSlots α) 𝕜).compContinuousLinearMap
    (fun t => ContinuousLinearMap.proj t.1)).smulRight c

@[simp] lemma monomialCMM_apply (α : ι → ℕ) (c : F) (v : MonomialSlots α → (ι → 𝕜)) :
    monomialCMM α c v = (∏ t : MonomialSlots α, v t t.1) • c := rfl

lemma monomialCMM_diag (α : ι → ℕ) (c : F) (z : ι → 𝕜) :
    monomialCMM α c (fun _ => z) = (∏ i, z i ^ α i) • c := by
  rw [monomialCMM_apply]
  congr 1
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => by simp

lemma norm_monomialCMM_le (α : ι → ℕ) (c : F) : ‖monomialCMM (𝕜 := 𝕜) α c‖ ≤ ‖c‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg c) fun v => ?_
  rw [monomialCMM_apply, norm_smul, norm_prod,
    mul_comm (∏ t : MonomialSlots α, ‖v t t.1‖) ‖c‖]
  gcongr with t
  exact norm_le_pi_norm (v t) t.1

lemma card_monomialSlots (α : ι → ℕ) : Fintype.card (MonomialSlots α) = ∑ i, α i := by
  simp [MonomialSlots, Fintype.card_sigma]

/-- The formal multilinear series of the monomial `z ↦ (∏ i, z i ^ α i) • c`: the single
term `monomialCMM α c`, placed in degree `∑ i, α i`. -/
noncomputable def monomialSeries (α : ι → ℕ) (c : F) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F := fun n =>
  if h : Fintype.card (MonomialSlots α) = n then
    (monomialCMM α c).domDomCongr (Fintype.equivFinOfCardEq h) else 0

lemma monomialSeries_of_ne (α : ι → ℕ) (c : F) {n : ℕ} (h : ∑ i, α i ≠ n) :
    monomialSeries (𝕜 := 𝕜) α c n = 0 := by
  rw [monomialSeries, dif_neg]
  rwa [card_monomialSlots]

lemma norm_monomialSeries_le (α : ι → ℕ) (c : F) (n : ℕ) :
    ‖monomialSeries (𝕜 := 𝕜) α c n‖ ≤ ‖c‖ := by
  rw [monomialSeries]
  split
  · rw [ContinuousMultilinearMap.norm_domDomCongr]
    exact norm_monomialCMM_le α c
  · simpa using norm_nonneg c

lemma monomialSeries_diag (α : ι → ℕ) (c : F) (z : ι → 𝕜) :
    monomialSeries α c (∑ i, α i) (fun _ => z) = (∏ i, z i ^ α i) • c := by
  rw [monomialSeries, dif_pos (card_monomialSlots α)]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact monomialCMM_diag α c z

/-- The one-term series really is the power series of the monomial, on any ball. -/
lemma hasFPowerSeriesOnBall_monomial (α : ι → ℕ) (c : F) {r : ℝ≥0} (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun z : ι → 𝕜 => (∏ i, z i ^ α i) • c) (monomialSeries α c) 0 r := by
  refine ⟨?_, by exact_mod_cast hr, fun {y} _ => ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ (‖c‖ * (r : ℝ) ^ (∑ i, α i)) fun n => ?_
    rcases eq_or_ne (∑ i, α i) n with h | h
    · subst h
      exact mul_le_mul_of_nonneg_right (norm_monomialSeries_le α c _) (by positivity)
    · rw [monomialSeries_of_ne α c h, norm_zero, zero_mul]
      positivity
  · have hvanish : ∀ n, n ≠ ∑ i, α i → (monomialSeries α c n fun _ : Fin n => y) = 0 := by
      intro n hn
      rw [monomialSeries_of_ne α c (Ne.symm hn)]
      simp
    simpa [monomialSeries_diag] using hasSum_single (f := fun n => monomialSeries α c n
      fun _ : Fin n => y) (∑ i, α i) hvanish

/-- **A normally convergent power series in several variables is analytic.**

If the coefficients `c α`, indexed by multi-indices `α : ι → ℕ`, satisfy
`∑ α, ‖c α‖ * r ^ |α| < ∞`, then `z ↦ ∑' α, z ^ α • c α` is analytic at the origin. -/
theorem analyticAt_tsum_monomial [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) 0 := by
  refine analyticAt_tsum hr (fun α => hasFPowerSeriesOnBall_monomial α (c α) hr) ?_
  set e : (ι → ℕ) → ℕ × (ι → ℕ) := fun α => (∑ j, α j, α) with he
  have hinj : Function.Injective e := fun a b h => by simpa [he] using congrArg Prod.snd h
  have hzero : ∀ kα : ℕ × (ι → ℕ), kα ∉ Set.range e →
      ‖monomialSeries (𝕜 := 𝕜) kα.2 (c kα.2) kα.1‖ * (r : ℝ) ^ kα.1 = 0 := by
    rintro ⟨k, α⟩ hk
    have hne : ∑ j, α j ≠ k := fun h => hk ⟨α, by simp [he, h]⟩
    rw [monomialSeries_of_ne α (c α) hne, norm_zero, zero_mul]
  rw [← hinj.summable_iff hzero]
  simp only [Function.comp_def]
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum
  exact mul_le_mul_of_nonneg_right (norm_monomialSeries_le _ _ _) (by positivity)

end
