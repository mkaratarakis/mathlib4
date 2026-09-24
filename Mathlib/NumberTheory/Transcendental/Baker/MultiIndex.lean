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

/-- The multi-index geometric family is summable.  This is what makes
`analyticAt_tsum_monomial` applicable in practice: Cauchy's inequalities bound the
coefficients by a constant times `R ^ (-|α|)`, and any `r < R` then gives a summable
family. -/
lemma summable_pow_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun α : ι → ℕ => q ^ (∑ i, α i) := by
  classical
  have hgeom : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ := hasSum_geometric_of_lt_one hq0 hq1
  have hgs : Summable fun n : ℕ => q ^ n := hgeom.summable
  refine summable_of_sum_le (c := ∏ _i : ι, (1 - q)⁻¹) (fun α => by positivity) fun S => ?_
  set N : ℕ := S.sup fun α => Finset.univ.sup α with hN
  have hsub : S ⊆ Fintype.piFinset fun _ : ι => Finset.range (N + 1) := by
    intro α hα
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have h1 : α i ≤ Finset.univ.sup α := Finset.le_sup (Finset.mem_univ i)
    have h2 : Finset.univ.sup α ≤ N := Finset.le_sup hα
    omega
  calc ∑ α ∈ S, q ^ (∑ i, α i)
      ≤ ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (N + 1), q ^ (∑ i, α i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun α _ _ => by positivity
    _ = ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (N + 1), ∏ i, q ^ α i :=
        Finset.sum_congr rfl fun α _ => by rw [← Finset.prod_pow_eq_pow_sum]
    _ = ∏ _i : ι, ∑ k ∈ Finset.range (N + 1), q ^ k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, (1 - q)⁻¹ := by
        gcongr
        · exact fun i _ => Finset.sum_nonneg fun k _ => by positivity
        · exact (hgs.sum_le_tsum _ fun n _ => by positivity).trans_eq hgeom.tsum_eq

/-- Cauchy-type coefficient bounds give a summable family on any smaller polydisc. -/
lemma summable_norm_mul_pow {c : (ι → ℕ) → F} {M R r : ℝ} (hR : 0 < R) (hr0 : 0 ≤ r)
    (hrR : r < R) (hc : ∀ α, ‖c α‖ ≤ M / R ^ (∑ i, α i)) :
    Summable fun α : ι → ℕ => ‖c α‖ * r ^ (∑ i, α i) := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (c 0)) (by simpa using hc 0)
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
    ((summable_pow_sum (ι := ι) (div_nonneg hr0 hR.le) ((div_lt_one hR).2 hrR)).mul_left M)
  have hRpow : (0 : ℝ) < R ^ (∑ i, α i) := by positivity
  calc ‖c α‖ * r ^ (∑ i, α i) ≤ (M / R ^ (∑ i, α i)) * r ^ (∑ i, α i) := by
        gcongr; exact hc α
    _ = M * (r / R) ^ (∑ i, α i) := by rw [div_pow]; field_simp

end
