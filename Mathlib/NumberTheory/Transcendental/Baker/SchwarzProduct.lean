/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.MultiIndex
public import Mathlib.NumberTheory.Transcendental.Baker.Polydisc

/-!
# Schwarz's lemma for Cartesian products

A function analytic on the polydisc of polyradius `R` in `ℂⁿ` and vanishing to order `m` in
each coordinate at every point of a product `E₁ × ⋯ × Eₙ` of finite sets in the disc of
radius `r` is small on the polydisc of polyradius `r`.  This is Proposition 4.7 of Waldschmidt,
*Diophantine Approximation on Linear Algebraic Groups*.

## Taylor coefficients at a point

`MultiIndex.taylorCoeff f x α` is the coefficient of `(z - x) ^ α` in the expansion of `f` about
`x`, that is `D^α f (x) / α!`.  It is defined from any power series of `f` at `x`; the choice
does not matter (`MultiIndex.coeff_eq_of_hasFPowerSeriesAt`).  Working with these coefficients
rather than with partial derivatives avoids a multi-index derivative API, which mathlib does
not have.

## Division by a linear factor

`MultiIndex.analyticAt_dslope_slice_of_eq` shows that the divided difference of `f` in the
`i`-th coordinate at `ζ` is analytic also on the hyperplane `z i = ζ`, where it is a
derivative; off the hyperplane this is `MultiIndex.analyticAt_dslope_slice_of_ne`.
-/

@[expose] public section

open Metric Function Filter Topology
open scoped NNReal ENNReal

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-!
### Taylor coefficients at a point
-/

omit [CompleteSpace F] in
lemma coeff_sub (p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    coeff (p - q) α = coeff p α - coeff q α := by
  simp [coeff, coeffAt, Finset.sum_sub_distrib]

omit [CompleteSpace F] in
/-- Two power series of the same function at the same point have the same multi-index
coefficients. -/
theorem coeff_eq_of_hasFPowerSeriesAt {f : (ι → 𝕜) → F}
    {p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜}
    (hp : HasFPowerSeriesAt f p x) (hq : HasFPowerSeriesAt f q x) (α : ι → ℕ) :
    coeff p α = coeff q α := by
  have h := hp.sub hq
  have h0 : (f - f) =ᶠ[𝓝 x] 0 := Eventually.of_forall fun _ => by simp
  rw [← sub_eq_zero, ← coeff_sub]
  exact coeffAt_eq_zero_of_eventuallyEq_zero h h0 (∑ i, α i) α

/-- The Taylor coefficient of `f` at `x` of multi-index `α`: the coefficient of `(z - x) ^ α`
in the expansion of `f` about `x`, that is `D^α f (x) / α!`.  It is `0` where `f` is not
analytic. -/
noncomputable def taylorCoeff (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) : F :=
  have := Classical.dec (AnalyticAt 𝕜 f x)
  if h : AnalyticAt 𝕜 f x then coeff h.choose α else 0

omit [CompleteSpace F] in
theorem taylorCoeff_eq {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {x : ι → 𝕜} (hp : HasFPowerSeriesAt f p x) (α : ι → ℕ) :
    taylorCoeff f x α = coeff p α := by
  have h : AnalyticAt 𝕜 f x := ⟨p, hp⟩
  simp only [taylorCoeff, h, ↓reduceDIte]
  exact coeff_eq_of_hasFPowerSeriesAt h.choose_spec hp α

omit [CompleteSpace F] in
theorem taylorCoeff_congr {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (h : f =ᶠ[𝓝 x] g) :
    taylorCoeff f x = taylorCoeff g x := by
  funext α
  by_cases hf : AnalyticAt 𝕜 f x
  · obtain ⟨p, hp⟩ := hf
    rw [taylorCoeff_eq hp, taylorCoeff_eq (hp.congr h)]
  · have hg : ¬ AnalyticAt 𝕜 g x := fun hg => hf (hg.congr h.symm)
    simp [taylorCoeff, hf, hg]

omit [CompleteSpace F] in
theorem taylorCoeff_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    taylorCoeff (f + g) x α = taylorCoeff f x α + taylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [taylorCoeff_eq (hp.add hq), taylorCoeff_eq hp, taylorCoeff_eq hq]
  simp [coeff, coeffAt, Finset.sum_add_distrib]

omit [CompleteSpace F] in
theorem taylorCoeff_sub {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    taylorCoeff (f - g) x α = taylorCoeff f x α - taylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [taylorCoeff_eq (hp.sub hq), taylorCoeff_eq hp, taylorCoeff_eq hq, coeff_sub]

omit [CompleteSpace F] in
theorem taylorCoeff_zero (x : ι → 𝕜) (α : ι → ℕ) :
    taylorCoeff (0 : (ι → 𝕜) → F) x α = 0 := by
  have h : HasFPowerSeriesAt (0 : (ι → 𝕜) → F) (0 : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) x := by
    have := (hasFPowerSeriesOnBall_const (𝕜 := 𝕜) (c := (0 : F)) (e := x)).hasFPowerSeriesAt
    rwa [constFormalMultilinearSeries_zero] at this
  rw [taylorCoeff_eq h]
  simp [coeff, coeffAt]

omit [CompleteSpace F] in
theorem taylorCoeff_finset_sum {β : Type*} (s : Finset β) {f : β → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ∀ b ∈ s, AnalyticAt 𝕜 (f b) x) (α : ι → ℕ) :
    taylorCoeff (fun z => ∑ b ∈ s, f b z) x α = ∑ b ∈ s, taylorCoeff (f b) x α := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact taylorCoeff_zero x α
  | insert a s ha ih =>
    have hs : AnalyticAt 𝕜 (fun z => ∑ b ∈ s, f b z) x :=
      Finset.analyticAt_fun_sum _ fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have hsplit : (fun z => ∑ b ∈ insert a s, f b z) = f a + fun z => ∑ b ∈ s, f b z := by
      funext z; simp [Finset.sum_insert ha]
    rw [hsplit, taylorCoeff_add (hf a (Finset.mem_insert_self a s)) hs, Finset.sum_insert ha,
      ih fun b hb => hf b (Finset.mem_insert_of_mem hb)]

omit [DecidableEq ι] [CompleteSpace F] in
private lemma norm_lt_of_mem_eball {y : ι → 𝕜} {ρ : ℝ≥0} (hy : y ∈ eball (0 : ι → 𝕜) ρ) :
    ‖y‖ < ρ := by
  rw [mem_eball_zero_iff, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hy
  exact_mod_cast hy

omit [DecidableEq ι] [CompleteSpace F] in
private lemma mem_eball_of_norm_lt {y : ι → 𝕜} {ρ : ℝ≥0} (hy : ‖y‖ < ρ) :
    y ∈ eball (0 : ι → 𝕜) ρ := by
  rw [mem_eball_zero_iff, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
  exact_mod_cast hy

/-- **Coefficients from an expansion.**  If `f (x + y)` is the sum of a normally convergent
multi-index power series on a polydisc, its coefficients are the Taylor coefficients of `f`
at `x`. -/
theorem taylorCoeff_eq_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜} {c : (ι → ℕ) → F}
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hsum : Summable fun α : ι → ℕ => ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i))
    (h : ∀ y : ι → 𝕜, ‖y‖ < ρ →
      HasSum (fun α : ι → ℕ => (∏ i, y i ^ α i) • c α) (f (x + y)))
    (α : ι → ℕ) : taylorCoeff f x α = c α := by
  have hP := hasFPowerSeriesOnBall_tsum_monomial (𝕜 := 𝕜) c hρ hsum
  have hP' : HasFPowerSeriesOnBall (fun y => f (x + y))
      (fun k => ∑' β : ι → ℕ, MultiIndex.series β (c β) k) 0 ρ :=
    hP.congr fun y hy => (h y (norm_lt_of_mem_eball hy)).tsum_eq
  have hPx := hP'.comp_sub x
  simp only [add_sub_cancel, zero_add] at hPx
  rw [taylorCoeff_eq hPx.hasFPowerSeriesAt]
  exact coeffAt_tsum_series c (card_slots α)

/-- **Local multi-index expansion.**  An analytic function is, on some polydisc about the
point, the sum of its normally convergent multi-index Taylor series. -/
theorem exists_hasSum_of_analyticAt {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      Summable (fun α : ι → ℕ => ‖taylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ i, α i)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ →
        HasSum (fun α : ι → ℕ => (∏ i, y i ^ α i) • taylorCoeff f x α) (f (x + y)) := by
  obtain ⟨p, r, hp⟩ := hf
  have hp0 : HasFPowerSeriesOnBall (fun y => f (x + y)) p 0 r := by
    have := hp.comp_sub (-x)
    simpa [add_comm, sub_eq_add_neg] using this
  obtain ⟨r₁, hr₁0, hr₁r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hr₁0' : (0 : ℝ≥0) < r₁ := by exact_mod_cast hr₁0
  set ρ : ℝ≥0 := r₁ / (Fintype.card ι + 2) with hρ
  have hρ0 : 0 < ρ := div_pos hr₁0' (by positivity)
  have hcardρ : (Fintype.card ι : ℝ≥0) * ρ < r₁ := by
    rw [hρ, ← NNReal.coe_lt_coe]
    push_cast
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) < r₁ := by exact_mod_cast hr₁0'
    nlinarith
  have hconv : ∀ t : ℝ≥0, t ≤ ρ →
      Summable fun k => (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (t : ℝ) ^ k := by
    intro t ht
    have hlt : (((Fintype.card ι : ℝ≥0) * t : ℝ≥0) : ℝ≥0∞) < p.radius := by
      refine lt_of_le_of_lt ?_ (hr₁r.trans_le hp.r_le)
      exact_mod_cast (mul_le_mul_of_nonneg_left ht (by positivity)).trans hcardρ.le
    refine (p.summable_norm_mul_pow hlt).congr fun k => ?_
    push_cast
    rw [mul_pow]
    ring
  have hsum := summable_norm_coeff_mul_pow p ρ.2 (hconv ρ le_rfl)
  have hρr₁ : ρ < r₁ := by
    rw [hρ]
    exact div_lt_self hr₁0'
      (lt_of_lt_of_le (by norm_num : (1 : ℝ≥0) < 2) (le_add_of_nonneg_left (by positivity)))
  have hp1 : HasFPowerSeriesOnBall (fun y => f (x + y)) p 0 r₁ :=
    hp0.mono (by exact_mod_cast hr₁0') hr₁r.le
  have htc : ∀ α, taylorCoeff f x α = coeff p α := taylorCoeff_eq hp.hasFPowerSeriesAt
  refine ⟨ρ, hρ0, by simpa [htc] using hsum, fun y hy => ?_⟩
  have hy₁ : ‖y‖ < (r₁ : ℝ) := hy.trans (by exact_mod_cast hρr₁)
  have hyρ : ‖y‖₊ ≤ ρ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hy.le
  have := hasSum_coeff hp1 hy₁ (by simpa using hconv ‖y‖₊ hyρ)
  simpa [htc] using this

/-!
### Division by a linear factor
-/

omit [DecidableEq ι] [CompleteSpace F] in
/-- The restriction of `f` to the hyperplane `z i = ζ`, as a function on the whole space. -/
lemma analyticAt_comp_update [DecidableEq ι] {f : (ι → 𝕜) → F} (i : ι) (ζ : 𝕜) {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f (update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => f (update z i ζ)) x := by
  have hupd : (fun z : ι → 𝕜 => update z i ζ)
      = fun z : ι → 𝕜 => z + (ζ - z i) • (Pi.single i 1 : ι → 𝕜) := by
    funext z j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj, Pi.single_eq_of_ne hj]
  have haff : AnalyticAt 𝕜 (fun z : ι → 𝕜 => update z i ζ) x := by
    rw [hupd]
    exact analyticAt_id.add ((analyticAt_const.sub
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).analyticAt x)).smul
        analyticAt_const)
  exact hf.comp_of_eq haff rfl

/-- **Division by a linear factor, across the hyperplane.**

If `f` is analytic at a point `x` of the hyperplane `z i = ζ`, then so is the divided
difference `z ↦ dslope (slice f i z) ζ (z i)`, which is `(f z - f (update z i ζ)) / (z i - ζ)`
off the hyperplane and the partial derivative on it.  In the multi-index expansion about `x` it
is the series with the `i`-th exponent shifted down by one. -/
theorem analyticAt_dslope_slice_of_eq {f : (ι → 𝕜) → F} (i : ι) {ζ : 𝕜} {x : ι → 𝕜}
    (hx : x i = ζ) (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) x := by
  obtain ⟨ρ, hρ, hsum, hhs⟩ := exists_hasSum_of_analyticAt hf
  set c := taylorCoeff f x with hc
  set G : (ι → 𝕜) → F := fun y =>
    ∑' β : ι → ℕ, (∏ j, y j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ)) with hG
  have hGan : AnalyticOnNhd 𝕜 G (eball 0 ρ) := analyticOnNhd_tsum_monomial_shift_pow c i 1 hρ hsum
  have hnorm_upd : ∀ (y : ι → 𝕜) (v : 𝕜), ‖v‖ ≤ ‖y‖ → ‖update y i v‖ ≤ ‖y‖ := by
    intro y v hv
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hv
    · rw [update_of_ne hj]; exact norm_le_pi_norm y j
  -- the splitting `f (x + y) = f (x + update y i 0) + y i • G y`
  have hsplit : ∀ y : ι → 𝕜, ‖y‖ < ρ → f (x + y) = f (x + update y i 0) + y i • G y := by
    intro y hy
    have h₁ : HasSum (fun β : ι → ℕ => (∏ j, y j ^ β j) • c (β + (Pi.single i 1 : ι → ℕ)))
        (G y) :=
      (summable_monomial_smul hy.le (summable_shift_pow (by exact_mod_cast hρ) i 1 hsum)).hasSum
    have hite : Summable fun α : ι → ℕ =>
        ‖(if α i = 0 then c α else 0)‖ * (ρ : ℝ) ^ (∑ j, α j) := by
      refine hsum.of_nonneg_of_le (fun _ => by positivity) fun α => ?_
      by_cases hα : α i = 0
      · simp [hα]
      · simp only [hα, ↓reduceIte, norm_zero, zero_mul]
        positivity
    have h₀ := (summable_monomial_smul hy.le hite).hasSum
    have hfull := hasSum_split_coord i h₀ h₁
    rw [(hhs y hy).unique hfull]
    congr 1
    rw [tsum_ite_coord_eq_update i y 0]
    have hy0 : ‖update y i 0‖ < ρ := (hnorm_upd y 0 (by simp)).trans_lt hy
    refine (tsum_congr fun α => ?_).trans (hhs _ hy0).tsum_eq
    by_cases hα : α i = 0
    · simp [hα]
    · rw [ite_eq_right_iff.2 (fun h => absurd h hα), smul_zero,
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hα]), zero_smul]
  have hq : ∀ y : ι → 𝕜, ‖y‖ < ρ → dslope (slice f i (x + y)) ζ ((x + y) i) = G y := by
    intro y hy
    have hxy : (x + y) i = ζ + y i := by simp [hx]
    have hupd : update (x + y) i ζ = x + update y i 0 := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp [hx]
      · simp [update_of_ne hj]
    rcases eq_or_ne (y i) 0 with hyi | hyi
    · -- on the hyperplane the divided difference is a derivative
      rw [hxy, hyi, add_zero, dslope_same]
      have hline : ∀ w : 𝕜,
          update (x + y) i w = x + (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) := by
        intro w
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [hx, hyi]
        · simp [update_of_ne hj, Pi.single_eq_of_ne hj]
      set φ : 𝕜 → F := fun w => G (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) with hφdef
      have hmem : ∀ᶠ w in 𝓝 ζ, ‖y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)‖ < ρ := by
        have hcont : Continuous fun w : 𝕜 => ‖y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)‖ := by
          fun_prop
        have h0 : ‖y + (ζ - ζ) • (Pi.single i 1 : ι → 𝕜)‖ < ρ := by simpa using hy
        exact hcont.continuousAt.eventually_lt continuousAt_const h0
      have hev : slice f i (x + y) =ᶠ[𝓝 ζ] fun w => f (x + y) + (w - ζ) • φ w := by
        filter_upwards [hmem] with w hw
        rw [slice, hline, hsplit _ hw]
        have hback : update (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) i 0 = y := by
          funext j
          rcases eq_or_ne j i with rfl | hj
          · simp [hyi]
          · simp [update_of_ne hj, Pi.single_eq_of_ne hj]
        have hcoord : (y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) i = w - ζ := by simp [hyi]
        rw [hback, hcoord]
      have hφ : DifferentiableAt 𝕜 φ ζ := by
        have hGy : AnalyticAt 𝕜 G (y + (ζ - ζ) • (Pi.single i 1 : ι → 𝕜)) :=
          hGan _ (mem_eball_of_norm_lt (by simpa using hy))
        have hlin : DifferentiableAt 𝕜 (fun w : 𝕜 => y + (w - ζ) • (Pi.single i 1 : ι → 𝕜)) ζ := by
          fun_prop
        exact hGy.differentiableAt.comp ζ hlin
      have hderiv : HasDerivAt (fun w => f (x + y) + (w - ζ) • φ w) (φ ζ) ζ := by
        have h1 : HasDerivAt (fun w : 𝕜 => w - ζ) 1 ζ := (hasDerivAt_id ζ).sub_const ζ
        simpa using (h1.smul hφ.hasDerivAt).const_add (f (x + y))
      rw [(hderiv.congr_of_eventuallyEq hev).deriv]
      simp [hφdef]
    · -- off the hyperplane it is the honest quotient
      have hkey := sub_smul_dslope_slice f i ζ (x + y)
      rw [hupd, hsplit y hy, add_sub_cancel_left, hxy, add_sub_cancel_left] at hkey
      rw [hxy]
      exact smul_right_injective F hyi hkey
  have hev : (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) =ᶠ[𝓝 x]
      fun z => G (z - x) := by
    filter_upwards [ball_mem_nhds x (by exact_mod_cast hρ : (0 : ℝ) < ρ)] with z hz
    have := hq (z - x) (by simpa [dist_eq_norm] using hz)
    simpa using this
  have hGx : AnalyticAt 𝕜 (fun z : ι → 𝕜 => G (z - x)) x :=
    (hGan 0 (mem_eball_of_norm_lt (by simpa using hρ))).comp_of_eq
      (analyticAt_id.sub analyticAt_const) (by simp)
  exact hGx.congr hev.symm

/-- **Division by a linear factor.**  The divided difference of an analytic function in one
coordinate is analytic, both on and off the hyperplane. -/
theorem analyticAt_dslope_slice {f : (ι → 𝕜) → F} (i : ι) (ζ : 𝕜) {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hres : AnalyticAt 𝕜 f (update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 => dslope (slice f i z) ζ (z i)) x := by
  rcases eq_or_ne (x i) ζ with h | h
  · exact analyticAt_dslope_slice_of_eq i h hf
  · exact analyticAt_dslope_slice_of_ne i ζ h hf (analyticAt_comp_update i ζ hres)

end MultiIndex
