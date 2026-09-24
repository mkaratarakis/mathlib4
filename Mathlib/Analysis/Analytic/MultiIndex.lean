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
  rw [MultiIndex.series, dite_eq_right]
  rwa [MultiIndex.card_slots]

lemma MultiIndex.norm_series_le (α : ι → ℕ) (c : F) (n : ℕ) :
    ‖MultiIndex.series (𝕜 := 𝕜) α c n‖ ≤ ‖c‖ := by
  rw [MultiIndex.series]
  split
  · rw [ContinuousMultilinearMap.norm_domDomCongr]
    exact MultiIndex.norm_toCMM_le α c
  · simp

lemma MultiIndex.series_diag (α : ι → ℕ) (c : F) (z : ι → 𝕜) :
    MultiIndex.series α c (∑ i, α i) (fun _ => z) = (∏ i, z i ^ α i) • c := by
  rw [MultiIndex.series, dite_eq_left (MultiIndex.card_slots α)]
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
    ((MultiIndex.summable_pow_sum (ι := ι) (div_nonneg hr0 hR.le)
      ((div_lt_one hR).2 hrR)).mul_left M)
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

namespace MultiIndex

/-- The multi-index recording how often each coordinate occurs in `g : Fin k → ι`. -/
def count [DecidableEq ι] {k : ℕ} (g : Fin k → ι) : ι → ℕ :=
  fun i => (Finset.univ.filter fun j => g j = i).card

lemma sum_count [DecidableEq ι] {k : ℕ} (g : Fin k → ι) : ∑ i, count g i = k :=
  (Finset.card_eq_sum_card_fiberwise (f := g) (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset ι)) fun x _ => Finset.mem_univ _).symm.trans (by simp)

omit [Fintype ι] in
lemma count_le [DecidableEq ι] {k : ℕ} (g : Fin k → ι) (i : ι) : count g i ≤ k := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin k)) fun j => g j = i
  rwa [Finset.card_univ, Fintype.card_fin] at h

lemma prod_eq_prod_pow_count [DecidableEq ι] {k : ℕ} (g : Fin k → ι) (z : ι → 𝕜) :
    ∏ j, z (g j) = ∏ i, z i ^ count g i := by
  rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset ι))
    (fun x _ => Finset.mem_univ (g x)) fun j => z (g j)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hconst : ∀ j ∈ Finset.univ.filter fun j => g j = i, z (g j) = z i := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    rw [hj.2]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const]
  rfl

end MultiIndex

/-- The coordinate expansion of a continuous multilinear map on the diagonal, regrouped by
multi-index.  Together with `analyticAt_tsum_monomial` this identifies analytic functions on
`ι → 𝕜` with normally convergent multi-index power series. -/
lemma ContinuousMultilinearMap.apply_diag_eq_sum_multiIndex [DecidableEq ι] {k : ℕ}
    (p : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => (ι → 𝕜)) F) (z : ι → 𝕜) :
    p (fun _ => z) = ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1),
      (∏ i, z i ^ α i) •
        ∑ g ∈ Finset.univ.filter fun g : Fin k → ι => MultiIndex.count g = α,
          p fun j => Pi.single (g j) 1 := by
  have hmaps : ∀ g : Fin k → ι, g ∈ (Finset.univ : Finset (Fin k → ι)) →
      MultiIndex.count g ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1) := by
    intro g _
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    exact fun i => Nat.lt_succ_of_le (MultiIndex.count_le g i)
  rw [p.apply_diag_eq_sum z, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  simp only [Finset.mem_filter] at hg
  rw [← hg.2, MultiIndex.prod_eq_prod_pow_count]

namespace MultiIndex

variable [DecidableEq ι]

/-- The degree-`k` multi-index coefficients of a formal multilinear series on `ι → 𝕜`: the
coefficient of `z ^ α` is the sum of the values of the `k`-th term on the tuples of basis
vectors whose coordinate counts are `α`.  It vanishes unless `α` has degree `k`. -/
noncomputable def coeffAt (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (k : ℕ) (α : ι → ℕ) : F :=
  ∑ g ∈ Finset.univ.filter fun g : Fin k → ι => count g = α, p k fun j => Pi.single (g j) 1

lemma coeffAt_eq_zero (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {k : ℕ} {α : ι → ℕ}
    (h : ∑ i, α i ≠ k) : coeffAt p k α = 0 := by
  rw [coeffAt, Finset.filter_eq_empty_iff.2, Finset.sum_empty]
  intro g _ hg
  exact h (hg ▸ sum_count g)

/-- Each coefficient is bounded by the size of its fibre times the norm of the term. -/
lemma norm_coeffAt_le (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (k : ℕ) (α : ι → ℕ) :
    ‖coeffAt p k α‖ ≤
      ((Finset.univ.filter fun g : Fin k → ι => count g = α).card : ℝ) * ‖p k‖ := by
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ g ∈ Finset.univ.filter fun g : Fin k → ι => count g = α,
      ‖p k fun j => (Pi.single (g j) 1 : ι → 𝕜)‖ ≤ ‖p k‖ := by
    intro g _
    have hm : ‖fun j : Fin k => (Pi.single (g j) 1 : ι → 𝕜)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by simp [Pi.norm_single]
    simpa using ContinuousMultilinearMap.le_opNorm_mul_pow_card_of_le _ hm
  simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hb

/-- The multi-index coefficients, at the degree of the multi-index. -/
noncomputable def coeff (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) : F :=
  coeffAt p (∑ i, α i) α

/-- The fibres of `count` in degree `k` partition the `(card ι) ^ k` tuples. -/
lemma sum_card_fiber (k : ℕ) :
    ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1),
      (Finset.univ.filter fun g : Fin k → ι => count g = α).card = Fintype.card ι ^ k := by
  have hmaps : Set.MapsTo (count (k := k))
      ((Finset.univ : Finset (Fin k → ι)) : Set (Fin k → ι))
      ((Fintype.piFinset fun _ : ι => Finset.range (k + 1) : Finset (ι → ℕ)) : Set (ι → ℕ)) := by
    intro g _
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    exact fun i => Nat.lt_succ_of_le (count_le g i)
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  exact h.symm

lemma coeffAt_eq_zero_of_notMem (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (k : ℕ) {α : ι → ℕ}
    (h : α ∉ Fintype.piFinset fun _ : ι => Finset.range (k + 1)) : coeffAt p k α = 0 := by
  rw [coeffAt, Finset.filter_eq_empty_iff.2, Finset.sum_empty]
  intro g _ hg
  refine h ?_
  simp only [Fintype.mem_piFinset, Finset.mem_range]
  intro i
  rw [← hg]
  exact Nat.lt_succ_of_le (count_le g i)

/-- In each degree, the coefficients total at most `(card ι) ^ k * ‖p k‖`. -/
lemma tsum_norm_coeffAt_le (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (k : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∑' α : ι → ℕ, ‖coeffAt p k α‖ * ρ ^ k ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k := by
  have hsupp : ∀ α ∉ Fintype.piFinset fun _ : ι => Finset.range (k + 1),
      ‖coeffAt p k α‖ * ρ ^ k = 0 := fun α hα => by
    rw [coeffAt_eq_zero_of_notMem p k hα, norm_zero, zero_mul]
  rw [tsum_eq_sum hsupp]
  calc ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1), ‖coeffAt p k α‖ * ρ ^ k
      ≤ ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1),
          (((Finset.univ.filter fun g : Fin k → ι => count g = α).card : ℝ) * ‖p k‖) * ρ ^ k := by
        refine Finset.sum_le_sum fun α _ => ?_
        exact mul_le_mul_of_nonneg_right (norm_coeffAt_le p k α) (by positivity)
    _ = ((∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1),
          ((Finset.univ.filter fun g : Fin k → ι => count g = α).card : ℝ))) * ‖p k‖ * ρ ^ k := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ = (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k := by
        rw [← Nat.cast_sum, sum_card_fiber]
        push_cast
        ring

lemma summable_prod_norm_coeffAt (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k) :
    Summable fun kα : ℕ × (ι → ℕ) => ‖coeffAt p kα.1 kα.2‖ * ρ ^ kα.1 := by
  rw [summable_prod_of_nonneg fun kα => by positivity]
  refine ⟨fun k => summable_of_ne_finset_zero (s := Fintype.piFinset fun _ : ι =>
    Finset.range (k + 1)) fun α hα => ?_, ?_⟩
  · rw [coeffAt_eq_zero_of_notMem p k hα, norm_zero, zero_mul]
  · exact Summable.of_nonneg_of_le (fun k => tsum_nonneg fun α => by positivity)
      (fun k => tsum_norm_coeffAt_le p k hρ) h

/-- **The coefficients of an analytic function on `ι → 𝕜` are normally summable.**  This is the
converse to `analyticAt_tsum_monomial`: it turns a `FormalMultilinearSeries` into a
multi-index power series, on any polydisc where `∑ (card ι) ^ k ‖p k‖ ρ ^ k` converges. -/
lemma summable_norm_coeff_mul_pow (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k) :
    Summable fun α : ι → ℕ => ‖coeff p α‖ * ρ ^ (∑ i, α i) := by
  have hinj : Function.Injective fun α : ι → ℕ => ((∑ i, α i), α) :=
    fun a b hab => by simpa using congrArg Prod.snd hab
  have hzero : ∀ kα : ℕ × (ι → ℕ), kα ∉ Set.range (fun α : ι → ℕ => ((∑ i, α i), α)) →
      ‖coeffAt p kα.1 kα.2‖ * ρ ^ kα.1 = 0 := by
    rintro ⟨k, α⟩ hk
    have hne : ∑ i, α i ≠ k := fun hh => hk ⟨α, by simp [hh]⟩
    rw [coeffAt_eq_zero p hne, norm_zero, zero_mul]
  have hs := (hinj.summable_iff hzero).2 (summable_prod_norm_coeffAt p hρ h)
  simpa [coeff, Function.comp_def] using hs

/-- **An analytic function on `ι → 𝕜` is the sum of its multi-index power series.**

This is the converse to `analyticAt_tsum_monomial`, and completes the identification of
analytic functions on a finite product of copies of `𝕜` with normally convergent
multi-index power series. -/
theorem hasSum_coeff [CompleteSpace F] {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {f : (ι → 𝕜) → F} {r : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p 0 r) {z : ι → 𝕜} (hz : ‖z‖ < r)
    (h : Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k) :
    HasSum (fun α : ι → ℕ => (∏ i, z i ^ α i) • coeff p α) (f z) := by
  classical
  set u : ℕ × (ι → ℕ) → F := fun kα => (∏ i, z i ^ kα.2 i) • coeffAt p kα.1 kα.2 with hu
  -- the doubly indexed family is dominated by the coefficient norms
  have hnorm : ∀ kα : ℕ × (ι → ℕ), ‖u kα‖ ≤ ‖coeffAt p kα.1 kα.2‖ * ‖z‖ ^ kα.1 := by
    rintro ⟨k, α⟩
    rcases eq_or_ne (∑ i, α i) k with hk | hk
    · subst hk
      rw [hu]
      simp only [norm_smul, norm_prod, norm_pow]
      rw [mul_comm]
      gcongr
      calc ∏ i, ‖z i‖ ^ α i ≤ ∏ i, ‖z‖ ^ α i := by
            gcongr with i
            exact norm_le_pi_norm z i
        _ = ‖z‖ ^ (∑ i, α i) := by rw [← Finset.prod_pow_eq_pow_sum]
    · simp [hu, coeffAt_eq_zero p hk]
  have hsummable : Summable u :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      (summable_prod_norm_coeffAt p (norm_nonneg z) h))
  -- in each degree the family sums to the corresponding term of the power series
  have hfib : ∀ k, HasSum (fun α : ι → ℕ => u (k, α)) (p k fun _ => z) := by
    intro k
    have hsupp : ∀ α ∉ Fintype.piFinset fun _ : ι => Finset.range (k + 1), u (k, α) = 0 :=
      fun α hα => by simp [hu, coeffAt_eq_zero_of_notMem p k hα]
    have hs : HasSum (fun α : ι → ℕ => u (k, α))
        (∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1), u (k, α)) :=
      hasSum_sum_of_ne_finset_zero hsupp
    have hkey : ∑ α ∈ Fintype.piFinset fun _ : ι => Finset.range (k + 1), u (k, α)
        = p k fun _ => z := by
      simp only [hu, coeffAt]
      exact ((p k).apply_diag_eq_sum_multiIndex z).symm
    rwa [hkey] at hs
  -- so the doubly indexed sum is `f z`
  have hball : z ∈ Metric.eball (0 : ι → 𝕜) r := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    exact_mod_cast hz
  have hfz : HasSum (fun k => p k fun _ => z) (f z) := by simpa using hf.hasSum hball
  have heq : (∑' kα, u kα) = f z := (hsummable.hasSum.prod_fiberwise hfib).unique hfz
  -- flatten along the degree
  have hinj : Function.Injective fun α : ι → ℕ => ((∑ i, α i), α) :=
    fun a b hab => by simpa using congrArg Prod.snd hab
  have hzero : ∀ kα : ℕ × (ι → ℕ), kα ∉ Set.range (fun α : ι → ℕ => ((∑ i, α i), α)) →
      u kα = 0 := by
    rintro ⟨k, α⟩ hk
    have hne : ∑ i, α i ≠ k := fun hh => hk ⟨α, by simp [hh]⟩
    simp [hu, coeffAt_eq_zero p hne]
  have hflat := (hinj.hasSum_iff hzero).2 hsummable.hasSum
  rw [heq] at hflat
  simpa [hu, coeff, Function.comp_def] using hflat

/-- **Division of a multi-index power series by a coordinate.**

If every coefficient supported off the `i`-th coordinate vanishes, then the series is `z i`
times the series with the `i`-th exponent shifted down.  This is the algebraic heart of the
division step in a Schwarz lemma for Cartesian products. -/
theorem hasSum_smul_shift {c : (ι → ℕ) → F} (i : ι) {z : ι → 𝕜} {T : F}
    (hvanish : ∀ α : ι → ℕ, α i = 0 → c α = 0)
    (h : HasSum (fun β : ι → ℕ => (∏ j, z j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ))) T) :
    HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (z i • T) := by
  set e : ι → ℕ := Pi.single i 1 with he
  -- multiplying the shifted series by `z i` restores the exponents
  have hterm : ∀ β : ι → ℕ,
      z i • ((∏ j, z j ^ β j) • c (β + e)) = (∏ j, z j ^ (β + e) j) • c (β + e) := by
    intro β
    rw [smul_smul]
    congr 1
    rw [show ∏ j, z j ^ (β + e) j = ∏ j, (z j ^ β j * z j ^ e j) from
      Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add], Finset.prod_mul_distrib]
    have : ∏ j, z j ^ e j = z i := by
      rw [Finset.prod_eq_single i]
      · simp [he]
      · intro j _ hj; simp [he, Pi.single_eq_of_ne hj]
      · simp
    rw [this, mul_comm]
  have hshift : HasSum (fun β : ι → ℕ => (∏ j, z j ^ (β + e) j) • c (β + e)) (z i • T) := by
    simpa [hterm] using h.const_smul (z i)
  -- reindex: the multi-indices missed by the shift have `α i = 0`, where `c` vanishes
  have hinj : Function.Injective fun β : ι → ℕ => β + e := add_left_injective e
  have hzero : ∀ α : ι → ℕ, α ∉ Set.range (fun β : ι → ℕ => β + e) →
      (∏ j, z j ^ α j) • c α = 0 := by
    intro α hα
    have hai : α i = 0 := by
      by_contra hne
      refine hα ⟨fun j => α j - e j, ?_⟩
      funext j
      simp only [Pi.add_apply]
      rcases eq_or_ne j i with rfl | hj
      · simp only [he, Pi.single_eq_same]
        omega
      · simp [he, Pi.single_eq_of_ne hj]
    rw [hvanish α hai, smul_zero]
  exact (hinj.hasSum_iff hzero).1 hshift

/-- The shifted series is again analytic: dividing by a coordinate preserves analyticity. -/
theorem analyticAt_tsum_monomial_shift [CompleteSpace F] (c : (ι → ℕ) → F)
    (i : ι) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ j, α j)) :
    AnalyticAt 𝕜
      (fun z : ι → 𝕜 => ∑' β : ι → ℕ, (∏ j, z j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ))) 0 :=
  analyticAt_tsum_monomial _ hr (MultiIndex.summable_shift (by exact_mod_cast hr) i hsum)

/-- **Splitting a multi-index power series along a coordinate.**

Every series decomposes as the part not involving `z i` plus `z i` times the shifted series.
This is the `p = 1` case of the division lemma behind a Schwarz lemma for Cartesian
products: `f = f₀ + z i * f₁` with `f₀` of degree `0` in `z i`. -/
theorem hasSum_split_coord {c : (ι → ℕ) → F} (i : ι) {z : ι → 𝕜} {S T : F}
    (h₀ : HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • (if α i = 0 then c α else 0)) S)
    (h₁ : HasSum (fun β : ι → ℕ =>
      (∏ j, z j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ))) T) :
    HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (S + z i • T) := by
  classical
  set d : (ι → ℕ) → F := fun α => if α i = 0 then 0 else c α with hd
  -- `d` is the part of `c` genuinely involving the `i`-th coordinate
  have hdvanish : ∀ α : ι → ℕ, α i = 0 → d α = 0 := fun α hα => by simp [hd, hα]
  have hdshift : ∀ β : ι → ℕ, d (β + (Pi.single i 1 : ι → ℕ)) = c (β + Pi.single i 1) := by
    intro β
    simp [hd]
  have h₁' : HasSum (fun β : ι → ℕ =>
      (∏ j, z j ^ β j) • d (β + (Pi.single i 1 : ι → ℕ))) T := by
    simpa [hdshift] using h₁
  have hsplit := h₀.add (hasSum_smul_shift i hdvanish h₁')
  refine hsplit.congr_fun fun α => ?_
  rw [← smul_add]
  congr 1
  by_cases hα : α i = 0 <;> simp [hd, hα]

/-- The part of a series not involving the `i`-th coordinate really does not: its value is
unchanged by moving `z i`. -/
theorem tsum_ite_coord_eq_update [CompleteSpace F] {c : (ι → ℕ) → F} (i : ι) (z : ι → 𝕜)
    (w : 𝕜) :
    (∑' α : ι → ℕ, (∏ j, z j ^ α j) • (if α i = 0 then c α else 0))
      = ∑' α : ι → ℕ, (∏ j, Function.update z i w j ^ α j) • (if α i = 0 then c α else 0) := by
  refine tsum_congr fun α => ?_
  by_cases hα : α i = 0
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rcases eq_or_ne j i with rfl | hj
    · rw [hα]; simp
    · rw [Function.update_of_ne hj]
  · simp [hα]

/-- **Division by a power of a coordinate.**

If every coefficient with `α i < p` vanishes, the series is `z i ^ p` times the series with
the `i`-th exponent shifted down by `p`.  This is `hasSum_smul_shift` iterated, and is the
induction on the degree in the division lemma behind a Schwarz lemma for Cartesian
products. -/
theorem hasSum_smul_shift_pow {c : (ι → ℕ) → F} (i : ι) {z : ι → 𝕜} :
    ∀ (p : ℕ) {T : F}, (∀ α : ι → ℕ, α i < p → c α = 0) →
      HasSum (fun β : ι → ℕ => (∏ j, z j ^ β j) • c (β + (Pi.single i p : ι → ℕ))) T →
      HasSum (fun α : ι → ℕ => (∏ j, z j ^ α j) • c α) (z i ^ p • T) := by
  intro p
  induction p generalizing c with
  | zero => intro T _ h; simpa using h
  | succ p ih =>
    intro T hvanish h
    -- peel off one factor, then apply the inductive hypothesis to the shifted coefficients
    have hstep : ∀ β : ι → ℕ,
        c (β + (Pi.single i p : ι → ℕ) + (Pi.single i 1 : ι → ℕ))
          = c (β + (Pi.single i (p + 1) : ι → ℕ)) := by
      intro β
      rw [add_assoc, ← Pi.single_add]
    have hshift : HasSum (fun β : ι → ℕ =>
        (∏ j, z j ^ β j) • (fun α => c (α + (Pi.single i 1 : ι → ℕ)))
          (β + (Pi.single i p : ι → ℕ))) T := by
      simpa [hstep] using h
    have hvanish' : ∀ β : ι → ℕ, β i < p → c (β + (Pi.single i 1 : ι → ℕ)) = 0 := by
      intro β hβ
      refine hvanish _ ?_
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    have hinner := ih (c := fun α => c (α + (Pi.single i 1 : ι → ℕ))) hvanish' hshift
    have houter := hasSum_smul_shift i (c := c) (fun α hα => hvanish α (by omega)) hinner
    rwa [smul_smul, ← pow_succ'] at houter

/-- Shifting a multi-index down by `p` in one coordinate keeps a series normally
convergent. -/
lemma summable_shift_pow {c : (ι → ℕ) → F} {r : ℝ} (hr : 0 < r) (i : ι) :
    ∀ (p : ℕ), (Summable fun α : ι → ℕ => ‖c α‖ * r ^ (∑ j, α j)) →
      Summable fun β : ι → ℕ => ‖c (β + (Pi.single i p : ι → ℕ))‖ * r ^ (∑ j, β j) := by
  intro p
  induction p generalizing c with
  | zero => intro hsum; simpa using hsum
  | succ p ih =>
    intro hsum
    have hstep : ∀ β : ι → ℕ,
        c (β + (Pi.single i p : ι → ℕ) + (Pi.single i 1 : ι → ℕ))
          = c (β + (Pi.single i (p + 1) : ι → ℕ)) := by
      intro β
      rw [add_assoc, ← Pi.single_add]
    have h1 := ih (c := fun α => c (α + (Pi.single i 1 : ι → ℕ))) (summable_shift hr i hsum)
    simpa [hstep] using h1

/-- The quotient of a normally convergent series by a power of a coordinate is again
analytic. -/
theorem analyticAt_tsum_monomial_shift_pow [CompleteSpace F] (c : (ι → ℕ) → F) (i : ι) (p : ℕ)
    {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (r : ℝ) ^ (∑ j, α j)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 =>
      ∑' β : ι → ℕ, (∏ j, z j ^ β j) • c (β + (Pi.single i p : ι → ℕ))) 0 :=
  analyticAt_tsum_monomial _ hr (summable_shift_pow (by exact_mod_cast hr) i p hsum)

omit [DecidableEq ι] in
/-- A normally convergent multi-index series converges at every point of the polydisc. -/
lemma summable_monomial_smul [CompleteSpace F] {c : (ι → ℕ) → F} {ρ : ℝ} {z : ι → 𝕜}
    (hz : ‖z‖ ≤ ρ) (hsum : Summable fun α : ι → ℕ => ‖c α‖ * ρ ^ (∑ j, α j)) :
    Summable fun α : ι → ℕ => (∏ j, z j ^ α j) • c α := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_) hsum)
  rw [norm_smul, norm_prod, mul_comm]
  gcongr
  calc ∏ j, ‖z j ^ α j‖ = ∏ j, ‖z j‖ ^ α j := by
        exact Finset.prod_congr rfl fun j _ => norm_pow _ _
    _ ≤ ∏ j, ρ ^ α j := by
        gcongr with j
        exact (norm_le_pi_norm z j).trans hz
    _ = ρ ^ (∑ j, α j) := by rw [← Finset.prod_pow_eq_pow_sum]

/-- **Division of an analytic function by a power of a coordinate.**

If the multi-index coefficients of `f` all vanish below degree `m` in the `i`-th coordinate,
then `f = z i ^ m • g` with `g` analytic. -/
theorem exists_analyticAt_eq_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {r : ℝ≥0} (hf : HasFPowerSeriesOnBall f p 0 r)
    (i : ι) (m : ℕ) (hvanish : ∀ α : ι → ℕ, α i < m → coeff p α = 0)
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hρr : (ρ : ℝ≥0∞) ≤ r)
    (hconv : ∀ z : ι → 𝕜, ‖z‖ ≤ (ρ : ℝ) →
      Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k)
    (hsum : Summable fun α : ι → ℕ => ‖coeff p α‖ * (ρ : ℝ) ^ (∑ j, α j)) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g 0 ∧
      ∀ z : ι → 𝕜, ‖z‖ < (ρ : ℝ) → f z = z i ^ m • g z := by
  refine ⟨fun z => ∑' β : ι → ℕ, (∏ j, z j ^ β j) • coeff p (β + (Pi.single i m : ι → ℕ)),
    analyticAt_tsum_monomial_shift_pow _ i m hρ hsum, fun z hz => ?_⟩
  have hshift : HasSum
      (fun β : ι → ℕ => (∏ j, z j ^ β j) • coeff p (β + (Pi.single i m : ι → ℕ)))
      (∑' β : ι → ℕ, (∏ j, z j ^ β j) • coeff p (β + (Pi.single i m : ι → ℕ))) :=
    (summable_monomial_smul hz.le (summable_shift_pow (by exact_mod_cast hρ) i m hsum)).hasSum
  have hfull := hasSum_smul_shift_pow (c := coeff p) i m hvanish hshift
  have hz' : ‖z‖ < (r : ℝ≥0) := by
    refine lt_of_lt_of_le hz ?_
    exact_mod_cast (ENNReal.coe_le_coe.1 hρr)
  exact (hasSum_coeff hf hz' (hconv z hz.le)).unique hfull

/-- **Division by a power of a coordinate, at a general centre.**

The same as `exists_analyticAt_eq_pow_smul` for a function analytic at `x`: if the
coefficients of the expansion at `x` vanish below degree `m` in the `i`-th coordinate, then
`f` is `(z i - x i) ^ m` times an analytic function.  Iterating this over the roots of a monic
polynomial `P` divides by `P (z i)`. -/
theorem exists_analyticAt_eq_sub_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (i : ι) (m : ℕ)
    (hvanish : ∀ α : ι → ℕ, α i < m → coeff p α = 0)
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hρr : (ρ : ℝ≥0∞) ≤ r)
    (hconv : ∀ z : ι → 𝕜, ‖z‖ ≤ (ρ : ℝ) →
      Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k)
    (hsum : Summable fun α : ι → ℕ => ‖coeff p α‖ * (ρ : ℝ) ^ (∑ j, α j)) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g 0 ∧
      ∀ z : ι → 𝕜, ‖z‖ < (ρ : ℝ) → f (x + z) = z i ^ m • g z := by
  have hf0 : HasFPowerSeriesOnBall (fun w : ι → 𝕜 => f (x + w)) p 0 r := by
    simpa [sub_neg_eq_add, add_comm] using hf.comp_sub (-x)
  exact exists_analyticAt_eq_pow_smul hf0 i m hvanish hρ hρr hconv hsum

end MultiIndex

end
