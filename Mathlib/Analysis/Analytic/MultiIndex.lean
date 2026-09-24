/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Analytic.Tsum

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

## Main statements

* `MultiIndex.series`: the one-term formal multilinear series of the monomial `z ^ α • c`.
* `MultiIndex.hasFPowerSeriesOnBall_series`: it is indeed its power series, on any ball.
* `analyticAt_tsum_monomial`: a normally convergent multi-index power series is analytic.
-/

@[expose] public section

open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The slots of the monomial `z ^ α`: one slot for each unit of each exponent. -/
abbrev MultiIndex.Slots (α : ι → ℕ) : Type _ := Σ i : ι, Fin (α i)

/-- The monomial `z ↦ (∏ i, z i ^ α i) • c`, as a continuous multilinear map with one
argument per slot; the slot `⟨i, _⟩` contributes the coordinate `i`. -/
noncomputable def MultiIndex.toCMM (α : ι → ℕ) (c : F) :
    ContinuousMultilinearMap 𝕜 (fun _ : MultiIndex.Slots α => (ι → 𝕜)) F :=
  ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 (MultiIndex.Slots α) 𝕜).compContinuousLinearMap
    (fun t => ContinuousLinearMap.proj t.1)).smulRight c

@[simp] lemma MultiIndex.toCMM_apply (α : ι → ℕ) (c : F) (v : MultiIndex.Slots α → (ι → 𝕜)) :
    MultiIndex.toCMM α c v = (∏ t : MultiIndex.Slots α, v t t.1) • c := rfl

lemma MultiIndex.toCMM_diag (α : ι → ℕ) (c : F) (z : ι → 𝕜) :
    MultiIndex.toCMM α c (fun _ => z) = (∏ i, z i ^ α i) • c := by
  rw [MultiIndex.toCMM_apply]
  congr 1
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => by simp

lemma MultiIndex.norm_toCMM_le (α : ι → ℕ) (c : F) : ‖MultiIndex.toCMM (𝕜 := 𝕜) α c‖ ≤ ‖c‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg c) fun v => ?_
  rw [MultiIndex.toCMM_apply, norm_smul, norm_prod,
    mul_comm (∏ t : MultiIndex.Slots α, ‖v t t.1‖) ‖c‖]
  gcongr with t
  exact norm_le_pi_norm (v t) t.1

lemma MultiIndex.card_slots (α : ι → ℕ) : Fintype.card (MultiIndex.Slots α) = ∑ i, α i := by
  simp [MultiIndex.Slots, Fintype.card_sigma]

/-- The formal multilinear series of the monomial `z ↦ (∏ i, z i ^ α i) • c`: the single
term `MultiIndex.toCMM α c`, placed in degree `∑ i, α i`. -/
noncomputable def MultiIndex.series (α : ι → ℕ) (c : F) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F := fun n =>
  if h : Fintype.card (MultiIndex.Slots α) = n then
    (MultiIndex.toCMM α c).domDomCongr (Fintype.equivFinOfCardEq h) else 0

lemma MultiIndex.series_of_ne (α : ι → ℕ) (c : F) {n : ℕ} (h : ∑ i, α i ≠ n) :
    MultiIndex.series (𝕜 := 𝕜) α c n = 0 := by
  rw [MultiIndex.series, dif_neg]
  rwa [MultiIndex.card_slots]

lemma MultiIndex.norm_series_le (α : ι → ℕ) (c : F) (n : ℕ) :
    ‖MultiIndex.series (𝕜 := 𝕜) α c n‖ ≤ ‖c‖ := by
  rw [MultiIndex.series]
  split
  · rw [ContinuousMultilinearMap.norm_domDomCongr]
    exact MultiIndex.norm_toCMM_le α c
  · simpa using norm_nonneg c

lemma MultiIndex.series_diag (α : ι → ℕ) (c : F) (z : ι → 𝕜) :
    MultiIndex.series α c (∑ i, α i) (fun _ => z) = (∏ i, z i ^ α i) • c := by
  rw [MultiIndex.series, dif_pos (MultiIndex.card_slots α)]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact MultiIndex.toCMM_diag α c z

/-- The one-term series really is the power series of the monomial, on any ball. -/
lemma MultiIndex.hasFPowerSeriesOnBall_series (α : ι → ℕ) (c : F) {r : ℝ≥0} (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun z : ι → 𝕜 => (∏ i, z i ^ α i) • c) (MultiIndex.series α c) 0 r := by
  refine ⟨?_, by exact_mod_cast hr, fun {y} _ => ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ (‖c‖ * (r : ℝ) ^ (∑ i, α i)) fun n => ?_
    rcases eq_or_ne (∑ i, α i) n with h | h
    · subst h
      exact mul_le_mul_of_nonneg_right (MultiIndex.norm_series_le α c _) (by positivity)
    · rw [MultiIndex.series_of_ne α c h, norm_zero, zero_mul]
      positivity
  · have hvanish : ∀ n, n ≠ ∑ i, α i → (MultiIndex.series α c n fun _ : Fin n => y) = 0 := by
      intro n hn
      rw [MultiIndex.series_of_ne α c (Ne.symm hn)]
      simp
    simpa [MultiIndex.series_diag] using hasSum_single (f := fun n => MultiIndex.series α c n
      fun _ : Fin n => y) (∑ i, α i) hvanish

/-- **A normally convergent power series in several variables is analytic.**

If the coefficients `c α`, indexed by multi-indices `α : ι → ℕ`, satisfy
`∑ α, ‖c α‖ * r ^ |α| < ∞`, then `z ↦ ∑' α, z ^ α • c α` is analytic at the origin. -/
theorem analyticAt_tsum_monomial [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) 0 := by
  refine analyticAt_tsum hr (fun α => MultiIndex.hasFPowerSeriesOnBall_series α (c α) hr) ?_
  set e : (ι → ℕ) → ℕ × (ι → ℕ) := fun α => (∑ j, α j, α) with he
  have hinj : Function.Injective e := fun a b h => by simpa [he] using congrArg Prod.snd h
  have hzero : ∀ kα : ℕ × (ι → ℕ), kα ∉ Set.range e →
      ‖MultiIndex.series (𝕜 := 𝕜) kα.2 (c kα.2) kα.1‖ * (r : ℝ) ^ kα.1 = 0 := by
    rintro ⟨k, α⟩ hk
    have hne : ∑ j, α j ≠ k := fun h => hk ⟨α, by simp [he, h]⟩
    rw [MultiIndex.series_of_ne α (c α) hne, norm_zero, zero_mul]
  rw [← hinj.summable_iff hzero]
  simp only [Function.comp_def]
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) hsum
  exact mul_le_mul_of_nonneg_right (MultiIndex.norm_series_le _ _ _) (by positivity)

/-- The multi-index geometric family is summable.  This is what makes
`analyticAt_tsum_monomial` applicable in practice: Cauchy's inequalities bound the
coefficients by a constant times `R ^ (-|α|)`, and any `r < R` then gives a summable
family. -/
lemma MultiIndex.summable_pow_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
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
lemma MultiIndex.summable_norm_mul_pow {c : (ι → ℕ) → F} {M R r : ℝ} (hR : 0 < R) (hr0 : 0 ≤ r)
    (hrR : r < R) (hc : ∀ α, ‖c α‖ ≤ M / R ^ (∑ i, α i)) :
    Summable fun α : ι → ℕ => ‖c α‖ * r ^ (∑ i, α i) := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (c 0)) (by simpa using hc 0)
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
    ((MultiIndex.summable_pow_sum (ι := ι) (div_nonneg hr0 hR.le) ((div_lt_one hR).2 hrR)).mul_left M)
  have hRpow : (0 : ℝ) < R ^ (∑ i, α i) := by positivity
  calc ‖c α‖ * r ^ (∑ i, α i) ≤ (M / R ^ (∑ i, α i)) * r ^ (∑ i, α i) := by
        gcongr; exact hc α
    _ = M * (r / R) ^ (∑ i, α i) := by rw [div_pow]; field_simp

/-- Expansion of a continuous multilinear map on the diagonal in coordinates: this is the
first half of the passage from a `FormalMultilinearSeries` on `ι → 𝕜` back to a
multi-indexed power series, the converse of `analyticAt_tsum_monomial`. -/
lemma ContinuousMultilinearMap.apply_diag_eq_sum [DecidableEq ι] {k : ℕ}
    (p : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => (ι → 𝕜)) F) (z : ι → 𝕜) :
    p (fun _ => z) = ∑ g : Fin k → ι, (∏ j, z (g j)) • p fun j => Pi.single (g j) 1 := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : ι → 𝕜) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    exact Finset.sum_congr rfl fun i _ => by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  calc p (fun _ => z)
      = p (fun _ : Fin k => ∑ i, z i • (Pi.single i 1 : ι → 𝕜)) := by rw [← hz]
    _ = ∑ g : Fin k → ι, p fun j => z (g j) • (Pi.single (g j) 1 : ι → 𝕜) :=
        p.map_sum fun _ i => z i • Pi.single i 1
    _ = ∑ g : Fin k → ι, (∏ j, z (g j)) • p fun j => Pi.single (g j) 1 :=
        Finset.sum_congr rfl fun g _ => p.map_smul_univ _ _

/-- Dividing a multi-index power series by a coordinate keeps it normally convergent:
the shifted coefficients `β ↦ c (β + eᵢ)` are summable on the same polydisc.  This is what
makes the division step of a Schwarz lemma for Cartesian products work. -/
lemma MultiIndex.summable_shift [DecidableEq ι] {c : (ι → ℕ) → F} {r : ℝ} (hr : 0 < r) (i : ι)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * r ^ (∑ j, α j)) :
    Summable fun β : ι → ℕ => ‖c (β + (Pi.single i 1 : ι → ℕ))‖ * r ^ (∑ j, β j) := by
  set e : ι → ℕ := Pi.single i 1 with he
  have hdeg : ∀ β : ι → ℕ, ∑ j, (β + e) j = (∑ j, β j) + 1 := fun β => by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    congr 1
    simp [he, Pi.single_apply]
  have h1 : Summable fun β : ι → ℕ => ‖c (β + e)‖ * r ^ (∑ j, (β + e) j) :=
    hsum.comp_injective (add_left_injective e)
  refine (h1.mul_right r⁻¹).congr fun β => ?_
  rw [hdeg]
  field_simp
  ring

end
