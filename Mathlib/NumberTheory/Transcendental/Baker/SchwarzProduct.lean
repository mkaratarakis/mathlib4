/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.NumberTheory.Transcendental.Baker.MultiIndex
public import Mathlib.NumberTheory.Transcendental.Baker.Polydisc
public import Mathlib.RingTheory.Coprime.Lemmas

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

/-!
### Newton division in one coordinate

Dividing successively by `z i - L 0, z i - L 1, …, z i - L (p - 1)` writes an analytic function
on a polydisc in Newton form
`g = ∑_{k < p} (∏_{l < k} (z i - L l)) • a k + (∏_{l < p} (z i - L l)) • q`, with `a k` not
depending on `z i`.  Each division costs a factor `2 / (R - r)` in the sup norm on the
polydisc of polyradius `R`, by the maximum modulus principle.
-/

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- `g` does not depend on the `j`-th coordinate. -/
def IndepOf (g : (ι → ℂ) → V) (j : ι) : Prop := ∀ (z : ι → ℂ) (w : ℂ), g (update z j w) = g z

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma indepOf_const (v : V) (j : ι) : IndepOf (fun _ : ι → ℂ => v) j := fun _ _ => rfl

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma indepOf_comp_update (g : (ι → ℂ) → V) (i : ι) (ζ : ℂ) :
    IndepOf (fun z => g (update z i ζ)) i := fun z w => by simp [update_idem]

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma IndepOf.comp_update {g : (ι → ℂ) → V} {i j : ι} (hji : j ≠ i) (hg : IndepOf g j) (ζ : ℂ) :
    IndepOf (fun z => g (update z i ζ)) j := fun z w => by
  simp only
  rw [update_comm hji, hg]

omit [Fintype ι] [CompleteSpace V] in
lemma IndepOf.dslope_slice {g : (ι → ℂ) → V} {i j : ι} (hji : j ≠ i) (hg : IndepOf g j)
    (ζ : ℂ) : IndepOf (fun z => dslope (slice g i z) ζ (z i)) j := fun z w => by
  have hsl : slice g i (update z j w) = slice g i z := by
    funext v
    simp only [slice]
    rw [update_comm hji, hg]
  simp only
  rw [hsl, update_of_ne hji.symm]

omit [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
lemma norm_update_le [DecidableEq ι] {y : ι → ℂ} {R : ℝ} (hy : ‖y‖ ≤ R) (i : ι) {v : ℂ}
    (hv : ‖v‖ ≤ R) : ‖update y i v‖ ≤ R := by
  have hR : 0 ≤ R := (norm_nonneg y).trans hy
  refine (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · simpa using hv
  · rw [update_of_ne hj]; exact (norm_le_pi_norm y j).trans hy

/-- **One division by a linear factor, with its estimate.**  On the polydisc of polyradius
`R`, the divided difference of `g` in the `i`-th coordinate at a point `ζ` of the disc of
radius `r < R` is analytic and bounded by `2 / (R - r)` times a bound for `g`. -/
theorem dslope_slice_bound {g : (ι → ℂ) → V} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (i : ι)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ r) (hg : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ g y) :
    (∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ (fun z => dslope (slice g i z) ζ (z i)) y) ∧
      ∀ M : ℝ, (∀ y : ι → ℂ, ‖y‖ ≤ R → ‖g y‖ ≤ M) →
        ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖dslope (slice g i y) ζ (y i)‖ ≤ 2 / (R - r) * M := by
  have hζR : ‖ζ‖ ≤ R := hζ.trans hrR.le
  have han : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ (fun z => dslope (slice g i z) ζ (z i)) y :=
    fun y hy => analyticAt_dslope_slice i ζ (hg y hy) (hg _ (norm_update_le hy i hζR))
  refine ⟨han, fun M hM y hy => ?_⟩
  have hbd := Complex.norm_le_of_eq_prod_smul (S := {ζ}) (m := 1) (M := 2 * M) hr hrR
    (by simpa using hζ) i han
    (f := fun z => g z - g (update z i ζ))
    (fun z _ => by simpa using (sub_smul_dslope_slice g i ζ z).symm)
    (fun z hz => (norm_sub_le _ _).trans (by
      linarith [hM z hz, hM _ (norm_update_le hz i hζR)])) y hy
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbd

/-- **Newton division in one coordinate.**

For nodes `L 0, L 1, …` in the disc of radius `r < R` and an analytic `g` on the polydisc of
polyradius `R`, there are analytic `a k` not depending on `z i`, and an analytic `q`, with
`g = ∑_{k < p} (∏_{l < k} (z i - L l)) • a k + (∏_{l < p} (z i - L l)) • q`.  If `‖g‖ ≤ M` then
`‖a k‖ ≤ (2 / (R - r)) ^ k * M` and `‖q‖ ≤ (2 / (R - r)) ^ p * M`; and `a k`, `q` do not depend
on any coordinate `j ≠ i` that `g` does not depend on. -/
theorem exists_newton {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (i : ι) :
    ∀ (p : ℕ) (L : ℕ → ℂ), (∀ k, ‖L k‖ ≤ r) → ∀ {g : (ι → ℂ) → V},
      (∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ g y) →
      ∃ (a : ℕ → (ι → ℂ) → V) (q : (ι → ℂ) → V),
        (∀ k (y : ι → ℂ), ‖y‖ ≤ R → AnalyticAt ℂ (a k) y) ∧
        (∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ q y) ∧
        (∀ k, IndepOf (a k) i) ∧
        (∀ j, j ≠ i → IndepOf g j → (∀ k, IndepOf (a k) j) ∧ IndepOf q j) ∧
        (∀ z : ι → ℂ, g z = ∑ k ∈ Finset.range p, (∏ l ∈ Finset.range k, (z i - L l)) • a k z +
          (∏ l ∈ Finset.range p, (z i - L l)) • q z) ∧
        ∀ M : ℝ, (∀ y : ι → ℂ, ‖y‖ ≤ R → ‖g y‖ ≤ M) →
          (∀ k < p, ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖a k y‖ ≤ (2 / (R - r)) ^ k * M) ∧
          ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖q y‖ ≤ (2 / (R - r)) ^ p * M := by
  intro p
  induction p with
  | zero =>
    intro L _ g hg
    refine ⟨fun _ _ => 0, g, fun _ _ _ => analyticAt_const, hg, fun _ => indepOf_const 0 i,
      fun j _ hgj => ⟨fun _ => indepOf_const 0 j, hgj⟩, fun z => by simp, fun M hM => ?_⟩
    exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun y hy => by simpa using hM y hy⟩
  | succ p ih =>
    intro L hL g hg
    have hL0R : ‖L 0‖ ≤ R := (hL 0).trans hrR.le
    set a₀ : (ι → ℂ) → V := fun z => g (update z i (L 0)) with ha₀
    obtain ⟨hg₁an, hg₁bd⟩ := dslope_slice_bound hr hrR i (hL 0) hg
    obtain ⟨a', q', ha'an, hq'an, ha'i, ha'j, hid, hbd⟩ :=
      ih (fun k => L (k + 1)) (fun k => hL (k + 1)) hg₁an
    refine ⟨fun k => if k = 0 then a₀ else a' (k - 1), q', fun k y hy => ?_, hq'an,
      fun k => ?_, fun j hji hgj => ?_, fun z => ?_, fun M hM => ?_⟩
    · by_cases hk : k = 0
      · simp only [hk, ↓reduceIte]
        exact analyticAt_comp_update i (L 0) (hg _ (norm_update_le hy i hL0R))
      · simp only [hk, ↓reduceIte]
        exact ha'an _ y hy
    · by_cases hk : k = 0
      · simp only [hk, ↓reduceIte]
        exact indepOf_comp_update g i (L 0)
      · simp only [hk, ↓reduceIte]
        exact ha'i _
    · obtain ⟨h1, h2⟩ := ha'j j hji (hgj.dslope_slice hji (L 0))
      refine ⟨fun k => ?_, h2⟩
      by_cases hk : k = 0
      · simp only [hk, ↓reduceIte]
        exact hgj.comp_update hji (L 0)
      · simp only [hk, ↓reduceIte]
        exact h1 _
    · have hstep : g z = a₀ z + (z i - L 0) • dslope (slice g i z) (L 0) (z i) := by
        rw [ha₀, sub_smul_dslope_slice]
        abel
      rw [hstep, hid z, Finset.sum_range_succ', Finset.prod_range_succ']
      simp only [Finset.prod_range_zero, one_smul, ↓reduceIte,
        Nat.add_sub_cancel, Nat.succ_ne_zero]
      rw [smul_add, Finset.smul_sum]
      have hterm : ∀ k ∈ Finset.range p,
          (z i - L 0) • (∏ l ∈ Finset.range k, (z i - L (l + 1))) • a' k z
            = (∏ l ∈ Finset.range (k + 1), (z i - L l)) • a' k z := by
        intro k _
        rw [smul_smul, Finset.prod_range_succ', mul_comm]
      rw [Finset.sum_congr rfl hterm, smul_smul, mul_comm]
      abel
    · have hg₁M := hg₁bd M hM
      obtain ⟨hak, hq⟩ := hbd (2 / (R - r) * M) hg₁M
      refine ⟨fun k hk y hy => ?_, fun y hy => ?_⟩
      · by_cases hk0 : k = 0
        · simp only [hk0, ↓reduceIte, pow_zero, one_mul]
          exact hM _ (norm_update_le hy i hL0R)
        · simp only [hk0, ↓reduceIte]
          obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          have := hak k' (by omega) y hy
          simp only [Nat.succ_sub_one]
          calc ‖a' k' y‖ ≤ (2 / (R - r)) ^ k' * (2 / (R - r) * M) := this
            _ = (2 / (R - r)) ^ (k' + 1) * M := by ring
      · calc ‖q' y‖ ≤ (2 / (R - r)) ^ p * (2 / (R - r) * M) := hq y hy
          _ = (2 / (R - r)) ^ (p + 1) * M := by ring

end MultiIndex

/-!
### Newton division in all coordinates

Applying `exists_newton` coordinate by coordinate writes `f` as a sum of a *main term*, a
combination of products of Newton basis polynomials in the separate coordinates, and one
*error term* `(∏_{l < p} (z i - L i l)) • Q i` for each coordinate.  Once every coordinate has
been processed the coefficients of the main term are constants.
-/

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The Newton basis polynomial `∏_{l < k} (z j - L j l)` in the `j`-th coordinate. -/
def nodeProd (L : ι → ℕ → ℂ) (j : ι) (k : ℕ) (z : ι → ℂ) : ℂ :=
  ∏ l ∈ Finset.range k, (z j - L j l)

omit [DecidableEq ι] in
lemma analyticAt_nodeProd (L : ι → ℕ → ℂ) (j : ι) (k : ℕ) (y : ι → ℂ) :
    AnalyticAt ℂ (nodeProd L j k) y :=
  Finset.analyticAt_fun_prod _ fun _ _ =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt y).sub
      analyticAt_const

omit [DecidableEq ι] in
lemma norm_nodeProd_le {L : ι → ℕ → ℂ} {r R : ℝ} (hL : ∀ j k, ‖L j k‖ ≤ r) (j : ι) (k : ℕ)
    {z : ι → ℂ} (hz : ‖z‖ ≤ R) : ‖nodeProd L j k z‖ ≤ (R + r) ^ k := by
  rw [nodeProd, norm_prod]
  calc ∏ l ∈ Finset.range k, ‖z j - L j l‖ ≤ ∏ _l ∈ Finset.range k, (R + r) := by
        gcongr with l hl
        exact (norm_sub_le _ _).trans (add_le_add ((norm_le_pi_norm z j).trans hz) (hL j l))
    _ = (R + r) ^ k := by simp

omit [Fintype ι] [DecidableEq ι] in
lemma nodeProd_update_of_ne (L : ι → ℕ → ℂ) {i j : ι} [DecidableEq ι] (hji : j ≠ i) (k : ℕ)
    (z : ι → ℂ) (w : ℂ) : nodeProd L j k (update z i w) = nodeProd L j k z := by
  simp [nodeProd, update_of_ne hji]

/-- The multi-indices with entries `< p` on `J` and `0` off `J`. -/
def boxH (J : Finset ι) (p : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun j => if j ∈ J then Finset.range p else {0}

lemma mem_boxH {J : Finset ι} {p : ℕ} {h : ι → ℕ} :
    h ∈ boxH J p ↔ ∀ j, (j ∈ J → h j < p) ∧ (j ∉ J → h j = 0) := by
  simp only [boxH, Fintype.mem_piFinset]
  refine forall_congr' fun j => ?_
  by_cases hj : j ∈ J <;> simp [hj]

lemma boxH_empty (p : ℕ) : boxH (∅ : Finset ι) p = {0} := by
  have : boxH (∅ : Finset ι) p = Fintype.piFinset fun j : ι => ({(0 : ι → ℕ) j} : Finset ℕ) := by
    simp [boxH]
  rw [this, Fintype.piFinset_singleton]

lemma boxH_univ (p : ℕ) : boxH (Finset.univ : Finset ι) p =
    Fintype.piFinset fun _ : ι => Finset.range p := by
  simp [boxH]

/-- Summing over `boxH (insert i₀ J)` is summing over `boxH J` and then over the new
coordinate. -/
lemma sum_boxH_insert {W : Type*} [AddCommMonoid W] {J : Finset ι} {i₀ : ι} (hi₀ : i₀ ∉ J)
    (p : ℕ) (g : (ι → ℕ) → W) :
    ∑ h ∈ boxH (insert i₀ J) p, g h =
      ∑ h ∈ boxH J p, ∑ k ∈ Finset.range p, g (update h i₀ k) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun h => (update h i₀ 0, h i₀)) (fun hk => update hk.1 i₀ hk.2)
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    rw [mem_boxH] at hh
    simp only [Finset.mem_product, Finset.mem_range, mem_boxH]
    refine ⟨fun j => ⟨fun hj => ?_, fun hj => ?_⟩, (hh i₀).1 (Finset.mem_insert_self _ _)⟩
    · rw [update_of_ne (by rintro rfl; exact hi₀ hj)]
      exact (hh j).1 (Finset.mem_insert_of_mem hj)
    · rcases eq_or_ne j i₀ with rfl | hj'
      · simp
      · rw [update_of_ne hj']
        exact (hh j).2 (by simp [hj, hj'])
  · rintro ⟨h, k⟩ hhk
    simp only [Finset.mem_product, Finset.mem_range, mem_boxH] at hhk
    rw [mem_boxH]
    intro j
    rcases eq_or_ne j i₀ with rfl | hj'
    · simp [hhk.2]
    · rw [update_of_ne hj']
      simp only [Finset.mem_insert, hj', false_or]
      exact hhk.1 j
  · intro h _
    simp
  · rintro ⟨h, k⟩ hhk
    simp only [Finset.mem_product, mem_boxH] at hhk
    have h0 : h i₀ = 0 := (hhk.1 i₀).2 hi₀
    simp only [update_idem, update_self, Prod.mk.injEq, and_true]
    rw [← h0, update_eq_self]
  · intro h _
    simp

/-- The sum over `boxH J p` of `∏_{j ∈ J} ρ ^ h j` is `(∑_{k < p} ρ ^ k) ^ card J`. -/
lemma sum_boxH_prod_pow (ρ : ℝ) (p : ℕ) (J : Finset ι) :
    ∑ h ∈ boxH J p, ∏ j ∈ J, ρ ^ h j = (∑ k ∈ Finset.range p, ρ ^ k) ^ J.card := by
  induction J using Finset.induction_on with
  | empty => simp [boxH_empty]
  | insert i₀ J hi₀ ih =>
    rw [sum_boxH_insert hi₀, Finset.card_insert_of_notMem hi₀, pow_succ, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h hh => ?_
    have h0 : h i₀ = 0 := ((mem_boxH.1 hh) i₀).2 hi₀
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_insert hi₀, update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [update_of_ne (by rintro rfl; exact hi₀ hj)]

omit [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
/-- A function depending on no coordinate is constant. -/
lemma eq_apply_zero_of_forall_indepOf [Finite ι] {g : (ι → ℂ) → V} (hg : ∀ j, IndepOf g j)
    (z : ι → ℂ) : g z = g 0 := by
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, g z = g fun j => if j ∈ s then 0 else z j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [ih]
      have hupd : (fun j => if j ∈ insert a s then (0 : ℂ) else z j)
          = update (fun j => if j ∈ s then (0 : ℂ) else z j) a 0 := by
        funext j
        rcases eq_or_ne j a with rfl | hja
        · simp
        · simp [hja]
      rw [hupd, hg a]
  simpa [Pi.zero_def] using key Finset.univ

/-- **Newton division in all coordinates of `J`.**  See the section docstring.  The constant
`K = 1 + ∑_{k < p} (2 (R + r) / (R - r)) ^ k` bounds the growth of the error terms. -/
theorem exists_newton_finset {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (p : ℕ) (L : ι → ℕ → ℂ)
    (hL : ∀ j k, ‖L j k‖ ≤ r) {f : (ι → ℂ) → V}
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ f y) {M : ℝ}
    (hM : ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖f y‖ ≤ M) (J : Finset ι) :
    ∃ (A : (ι → ℕ) → (ι → ℂ) → V) (Q : ι → (ι → ℂ) → V),
      (∀ h (y : ι → ℂ), ‖y‖ ≤ R → AnalyticAt ℂ (A h) y) ∧
      (∀ i (y : ι → ℂ), ‖y‖ ≤ R → AnalyticAt ℂ (Q i) y) ∧
      (∀ h, ∀ j ∈ J, IndepOf (A h) j) ∧
      (∀ h ∈ boxH J p, ∀ y : ι → ℂ, ‖y‖ ≤ R →
        ‖A h y‖ ≤ (∏ j ∈ J, (2 / (R - r)) ^ h j) * M) ∧
      (∀ i ∈ J, ∀ y : ι → ℂ, ‖y‖ ≤ R →
        ‖Q i y‖ ≤ (1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k) ^ J.card *
          (2 / (R - r)) ^ p * M) ∧
      ∀ z : ι → ℂ, f z = ∑ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) z) • A h z +
        ∑ i ∈ J, nodeProd L i p z • Q i z := by
  have hR : 0 < R := hr.trans_lt hrR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hR.le))
  have hc : 0 ≤ 2 / (R - r) := div_nonneg (by norm_num) (by linarith)
  set K := 1 + ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ k ∈ Finset.range p, (2 / (R - r) * (R + r)) ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg (mul_nonneg hc (by linarith)) k
    linarith
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => f, fun _ => 0, fun _ => hf, fun _ _ _ => analyticAt_const,
      fun _ j hj => absurd hj (Finset.notMem_empty j), fun h _ y hy => by simpa using hM y hy,
      fun i hi => absurd hi (Finset.notMem_empty i), fun z => by simp [boxH_empty]⟩
  | insert i₀ J hi₀ ih =>
    obtain ⟨A, Q, hA, hQ, hAind, hAbd, hQbd, hid⟩ := ih
    have hN := fun h => exists_newton (V := V) hr hrR i₀ p (L i₀) (hL i₀) (hA h)
    choose a q ha hq hai haj hdec hbd using hN
    set A' : (ι → ℕ) → (ι → ℂ) → V := fun h' => a (update h' i₀ 0) (h' i₀) with hA'
    set Q₀ : (ι → ℂ) → V :=
      fun z => ∑ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) z) • q h z with hQ₀
    set Q' : ι → (ι → ℂ) → V := fun i => if i = i₀ then Q₀ else Q i with hQ'
    refine ⟨A', Q', fun h' y hy => ha _ _ y hy, fun i y hy => ?_, fun h' j hj => ?_,
      fun h' hh' y hy => ?_, fun i hi y hy => ?_, fun z => ?_⟩
    · -- analyticity of the new error term
      by_cases hi : i = i₀
      · simp only [hQ', hi, ↓reduceIte, hQ₀]
        exact Finset.analyticAt_fun_sum _ fun h _ =>
          (Finset.analyticAt_fun_prod _ fun j _ => analyticAt_nodeProd L j _ y).smul
            (hq h y hy)
      · simp only [hQ', hi, ↓reduceIte]
        exact hQ i y hy
    · -- the new coefficients depend on no coordinate of `insert i₀ J`
      rcases Finset.mem_insert.1 hj with rfl | hjJ
      · exact hai _ _
      · exact (haj _ j (by rintro rfl; exact hi₀ hjJ) (hAind _ j hjJ)).1 _
    · -- bound on the new coefficients
      rw [mem_boxH] at hh'
      set h := update h' i₀ 0 with hh
      have hhmem : h ∈ boxH J p := by
        rw [mem_boxH]
        intro j
        refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [hh, update_of_ne (by rintro rfl; exact hi₀ hj)]
          exact (hh' j).1 (Finset.mem_insert_of_mem hj)
        · rcases eq_or_ne j i₀ with rfl | hj'
          · simp [hh]
          · rw [hh, update_of_ne hj']
            exact (hh' j).2 (by simp [hj, hj'])
      have hk : h' i₀ < p := (hh' i₀).1 (Finset.mem_insert_self _ _)
      have := ((hbd h _ (hAbd h hhmem)).1 (h' i₀) hk y hy)
      refine this.trans (le_of_eq ?_)
      rw [Finset.prod_insert hi₀, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hh, update_of_ne (by rintro rfl; exact hi₀ hj)]
    · -- bound on the error terms
      rw [Finset.card_insert_of_notMem hi₀]
      by_cases hii : i = i₀
      · simp only [hQ', hii, ↓reduceIte, hQ₀]
        have hterm : ∀ h ∈ boxH J p, ‖(∏ j ∈ J, nodeProd L j (h j) y) • q h y‖ ≤
            (2 / (R - r)) ^ p * M * ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j := by
          intro h hh
          rw [norm_smul, norm_prod]
          have hqh := (hbd h _ (hAbd h hh)).2 y hy
          calc (∏ j ∈ J, ‖nodeProd L j (h j) y‖) * ‖q h y‖
              ≤ (∏ j ∈ J, (R + r) ^ h j) *
                  ((2 / (R - r)) ^ p * ((∏ j ∈ J, (2 / (R - r)) ^ h j) * M)) := by
                gcongr with j hj
                exact norm_nodeProd_le hL j (h j) hy
            _ = (2 / (R - r)) ^ p * M * ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j := by
                rw [show ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j
                    = (∏ j ∈ J, (2 / (R - r)) ^ h j) * ∏ j ∈ J, (R + r) ^ h j by
                  rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]]
                ring
        calc ‖∑ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) y) • q h y‖
            ≤ ∑ h ∈ boxH J p, (2 / (R - r)) ^ p * M * ∏ j ∈ J, (2 / (R - r) * (R + r)) ^ h j :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
          _ = (2 / (R - r)) ^ p * M * (K - 1) ^ J.card := by
              rw [← Finset.mul_sum, sum_boxH_prod_pow, hK, add_sub_cancel_left]
          _ ≤ K ^ (J.card + 1) * (2 / (R - r)) ^ p * M := by
              have hKK : (K - 1) ^ J.card ≤ K ^ (J.card + 1) :=
                (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
                  (pow_le_pow_right₀ hK1 (Nat.le_succ _))
              have : 0 ≤ (2 / (R - r)) ^ p * M := mul_nonneg (pow_nonneg hc p) hM0
              nlinarith
      · simp only [hQ', hii, ↓reduceIte]
        have hiJ : i ∈ J := by simpa [hii] using hi
        refine (hQbd i hiJ y hy).trans ?_
        have : 0 ≤ (2 / (R - r)) ^ p * M := mul_nonneg (pow_nonneg hc p) hM0
        have hKK : K ^ J.card ≤ K ^ (J.card + 1) := pow_le_pow_right₀ hK1 (Nat.le_succ _)
        nlinarith
    · -- the identity
      rw [hid z, sum_boxH_insert hi₀, Finset.sum_insert hi₀]
      have hmain : ∀ h ∈ boxH J p, (∏ j ∈ J, nodeProd L j (h j) z) • A h z =
          ∑ k ∈ Finset.range p,
            (∏ j ∈ insert i₀ J, nodeProd L j (update h i₀ k j) z) • A' (update h i₀ k) z +
          nodeProd L i₀ p z • (∏ j ∈ J, nodeProd L j (h j) z) • q h z := by
        intro h hh
        have h0 : h i₀ = 0 := ((mem_boxH.1 hh) i₀).2 hi₀
        rw [hdec h z, smul_add, Finset.smul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hA'k : A' (update h i₀ k) = a h k := by
            simp only [hA', update_idem, update_self]
            rw [← h0, update_eq_self]
          rw [hA'k, Finset.prod_insert hi₀, update_self, smul_smul,
            show ∏ x ∈ J, nodeProd L x (update h i₀ k x) z = ∏ j ∈ J, nodeProd L j (h j) z from
              Finset.prod_congr rfl fun j hj => by
                rw [update_of_ne (by rintro rfl; exact hi₀ hj)], mul_comm]
          rfl
        · rw [smul_comm]
          rfl
      rw [Finset.sum_congr rfl hmain, Finset.sum_add_distrib, ← Finset.smul_sum]
      have hQJ : ∑ i ∈ J, nodeProd L i p z • Q' i z = ∑ i ∈ J, nodeProd L i p z • Q i z :=
        Finset.sum_congr rfl fun i hi => by
          simp only [hQ', show i ≠ i₀ by rintro rfl; exact hi₀ hi, ↓reduceIte]
      rw [hQJ]
      simp only [hQ', ↓reduceIte, hQ₀]
      abel

end MultiIndex

/-!
### Uniqueness of the main term

After all coordinates are processed, the main term is a polynomial with constant
coefficients in the tensor Newton basis.  If `f` vanishes to order `m` in each coordinate on
`E₁ × ⋯ × Eₙ` and the nodes in the `j`-th coordinate are the points of `E j`, each repeated
`m` times, these coefficients vanish.  In one variable this is root counting: a polynomial of
degree `< m * card E` with a root of multiplicity `≥ m` at each point of `E` is zero.  The
several-variable statement is the injectivity of a tensor product of injective maps.
-/

namespace MultiIndex

open Polynomial

/-- The Newton basis polynomial `∏_{l < k} (X - L l)`. -/
noncomputable def nodePoly (L : ℕ → ℂ) (k : ℕ) : ℂ[X] := ∏ l ∈ Finset.range k, (X - C (L l))

lemma nodePoly_monic (L : ℕ → ℂ) (k : ℕ) : (nodePoly L k).Monic :=
  monic_prod_of_monic _ _ fun l _ => monic_X_sub_C (L l)

lemma natDegree_nodePoly (L : ℕ → ℂ) (k : ℕ) : (nodePoly L k).natDegree = k := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C (L l)]
  simp

lemma eval_nodePoly (L : ℕ → ℂ) (k : ℕ) (w : ℂ) :
    (nodePoly L k).eval w = ∏ l ∈ Finset.range k, (w - L l) := by
  simp [nodePoly, eval_prod]

/-- The Newton basis is triangular: a vanishing combination has zero coefficients. -/
lemma eq_zero_of_sum_C_mul_nodePoly (L : ℕ → ℂ) : ∀ (p : ℕ) (a : ℕ → ℂ),
    ∑ k ∈ Finset.range p, C (a k) * nodePoly L k = 0 → ∀ k < p, a k = 0 := by
  intro p
  induction p with
  | zero => intro a _ k hk; omega
  | succ p ih =>
    intro a h k hk
    have h1 : (nodePoly L p).coeff p = 1 := by
      have := (nodePoly_monic L p).coeff_natDegree
      rwa [natDegree_nodePoly] at this
    have hlow : ∀ k ∈ Finset.range p, a k * (nodePoly L k).coeff p = 0 := fun k hk => by
      rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_nodePoly]; exact Finset.mem_range.1 hk),
        mul_zero]
    have htop : a p = 0 := by
      have hc := congrArg (fun P => P.coeff p) h
      simp only [Finset.sum_range_succ, coeff_add, coeff_C_mul, finsetSum_coeff,
        coeff_zero] at hc
      rwa [Finset.sum_eq_zero hlow, zero_add, h1, mul_one] at hc
    have hrest : ∑ k ∈ Finset.range p, C (a k) * nodePoly L k = 0 := by
      rwa [Finset.sum_range_succ, htop, C_0, zero_mul, add_zero] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih a hrest k hk
    · exact htop

/-- **Newton coefficients from Taylor data.**  Let the nodes `L 0, …, L (p - 1)` be the points
of `E`, each repeated `m` times.  If a combination `∑_{k < p} d k • ∏_{l < k} (X - L l)` has all
Taylor coefficients of order `< m` zero at every point of `E`, then every `d k` is zero. -/
theorem newton_eq_zero_of_taylor {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {L : ℕ → ℂ} {E : Finset ℂ} {m p : ℕ} (hLE : nodePoly L p = ∏ ζ ∈ E, (X - C ζ) ^ m)
    (d : ℕ → W)
    (hd : ∀ ζ ∈ E, ∀ t < m,
      ∑ k ∈ Finset.range p, (taylor ζ (nodePoly L k)).coeff t • d k = 0) :
    ∀ k < p, d k = 0 := by
  intro k hk
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ => ?_
  set a : ℕ → ℂ := fun k => φ (d k) with ha
  set Q : ℂ[X] := ∑ k ∈ Finset.range p, C (a k) * nodePoly L k with hQ
  have htay : ∀ ζ ∈ E, ∀ t < m, (taylor ζ Q).coeff t = 0 := by
    intro ζ hζ t ht
    have hφ := congrArg φ (hd ζ hζ t ht)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hφ
    rw [hQ]
    simp_rw [← smul_eq_C_mul]
    rw [map_sum, finsetSum_coeff]
    simp_rw [LinearMap.map_smul, coeff_smul, smul_eq_mul]
    rw [← hφ]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdvd : ∀ ζ ∈ E, (X - C ζ) ^ m ∣ Q := by
    intro ζ hζ
    by_cases hQ0 : Q = 0
    · rw [hQ0]; exact dvd_zero _
    · rw [← le_rootMultiplicity_iff hQ0, rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      exact le_natTrailingDegree (by rwa [Ne, taylor_eq_zero]) (htay ζ hζ)
  have hcop : (E : Set ℂ).Pairwise (IsCoprime on fun ζ => (X - C ζ) ^ m) := by
    intro a _ b _ hab
    exact ((pairwise_coprime_X_sub_C (s := id) injective_id) hab).pow
  have hprod : nodePoly L p ∣ Q := by
    rw [hLE]
    exact Finset.prod_dvd_of_coprime hcop hdvd
  have hdeg : Q.natDegree < (nodePoly L p).natDegree := by
    rw [natDegree_nodePoly]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p - 1) fun k hk => ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_nodePoly]
    have := Finset.mem_range.1 hk
    omega
  exact eq_zero_of_sum_C_mul_nodePoly L p a (eq_zero_of_dvd_of_natDegree_lt hprod hdeg) k hk

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma update_zero_mem_boxH {J : Finset ι} {i₀ : ι} (hi₀ : i₀ ∉ J) {p : ℕ} {h : ι → ℕ}
    (hh : h ∈ boxH (insert i₀ J) p) : update h i₀ 0 ∈ boxH J p := by
  rw [mem_boxH] at hh ⊢
  intro j
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · rw [update_of_ne (by rintro rfl; exact hi₀ hj)]
    exact (hh j).1 (Finset.mem_insert_of_mem hj)
  · rcases eq_or_ne j i₀ with rfl | hj'
    · simp
    · rw [update_of_ne hj']
      exact (hh j).2 (by simp [hj, hj'])

/-- **A tensor product of injective maps is injective.**  If, in each coordinate, a vector
`d : ℕ → W` supported below `p` is determined by the values `∑_k Mx j k γ • d k`, then a family
indexed by `boxH J p` is determined by the tensor products of these values. -/
theorem eq_zero_of_tensor {W : Type*} [AddCommGroup W] [Module ℂ W] {p : ℕ}
    {Cond : ι → Type*} [∀ j, Nonempty (Cond j)] (Mx : ∀ j, ℕ → Cond j → ℂ)
    (hinj : ∀ j (d : ℕ → W),
      (∀ γ : Cond j, ∑ k ∈ Finset.range p, Mx j k γ • d k = 0) → ∀ k < p, d k = 0)
    (J : Finset ι) : ∀ C : (ι → ℕ) → W,
      (∀ γ : ∀ j, Cond j, ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C h = 0) →
      ∀ h ∈ boxH J p, C h = 0 := by
  induction J using Finset.induction_on with
  | empty =>
    intro C hC h hh
    rw [boxH_empty, Finset.mem_singleton] at hh
    subst hh
    simpa [boxH_empty] using hC fun _ => Classical.arbitrary _
  | insert i₀ J hi₀ ih =>
    intro C hC h' hh'
    have hk : ∀ k < p, ∀ γ : ∀ j, Cond j,
        ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C (update h i₀ k) = 0 := by
      intro k hkp γ
      refine hinj i₀ (fun k =>
        ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C (update h i₀ k)) (fun γ₀ => ?_) k hkp
      calc ∑ k ∈ Finset.range p, Mx i₀ k γ₀ •
            ∑ h ∈ boxH J p, (∏ j ∈ J, Mx j (h j) (γ j)) • C (update h i₀ k)
          = ∑ h ∈ boxH J p, ∑ k ∈ Finset.range p,
              (∏ j ∈ insert i₀ J, Mx j (update h i₀ k j) (update γ i₀ γ₀ j)) •
                C (update h i₀ k) := by
            simp_rw [Finset.smul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => ?_
            rw [smul_smul, Finset.prod_insert hi₀, update_self, update_self]
            congr 2
            refine Finset.prod_congr rfl fun j hj => ?_
            have hj' : j ≠ i₀ := by rintro rfl; exact hi₀ hj
            rw [update_of_ne hj', update_of_ne hj']
        _ = 0 := (sum_boxH_insert hi₀ p fun h =>
              (∏ j ∈ insert i₀ J, Mx j (h j) (update γ i₀ γ₀ j)) • C h).symm.trans (hC _)
    have hmem := update_zero_mem_boxH hi₀ hh'
    have hlt : h' i₀ < p := ((mem_boxH.1 hh') i₀).1 (Finset.mem_insert_self _ _)
    have := ih (fun h => C (update h i₀ (h' i₀))) (hk _ hlt) _ hmem
    simpa [update_idem] using this

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- **The Taylor coefficients of the main term.**  At `ξ`, the coefficient of `(z - ξ) ^ κ` of
`∑_h (∏_j nodeProd L j (h j) z) • C₀ h` is the tensor combination of the one-variable Taylor
coefficients of the Newton basis polynomials. -/
theorem taylorCoeff_mainTerm (L : ι → ℕ → ℂ) (p : ℕ) (C₀ : (ι → ℕ) → V) (ξ : ι → ℂ)
    (κ : ι → ℕ) :
    taylorCoeff (fun z => ∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) z) • C₀ h) ξ κ =
      ∑ h ∈ boxH Finset.univ p,
        (∏ j, (taylor (ξ j) (nodePoly (L j) (h j))).coeff (κ j)) • C₀ h := by
  set c : (ι → ℕ) → V := fun κ => ∑ h ∈ boxH Finset.univ p,
    (∏ j, (taylor (ξ j) (nodePoly (L j) (h j))).coeff (κ j)) • C₀ h with hc
  set box : Finset (ι → ℕ) := Fintype.piFinset fun _ : ι => Finset.range (p + 1) with hbox
  have hc0 : ∀ κ ∉ box, c κ = 0 := by
    intro κ hκ
    obtain ⟨j, hj⟩ : ∃ j, p + 1 ≤ κ j := by
      by_contra hcon
      push Not at hcon
      exact hκ (by simpa [hbox, Fintype.mem_piFinset] using hcon)
    refine Finset.sum_eq_zero fun h hh => ?_
    have hhj : h j < p := ((mem_boxH.1 hh) j).1 (Finset.mem_univ j)
    rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_smul]
    exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor, natDegree_nodePoly]; omega)
  have hsum : Summable fun α : ι → ℕ => ‖c α‖ * ((1 : ℝ≥0) : ℝ) ^ (∑ i, α i) :=
    summable_of_ne_finset_zero (s := box) fun α hα => by simp [hc0 α hα]
  refine taylorCoeff_eq_of_hasSum (ρ := 1) one_pos hsum (fun y _ => ?_) κ
  have hfin : ∀ α ∉ box, (∏ i, y i ^ α i) • c α = 0 := fun α hα => by rw [hc0 α hα, smul_zero]
  have hN : ∀ h ∈ boxH Finset.univ p, ∀ j, nodeProd L j (h j) (ξ + y) =
      ∑ t ∈ Finset.range (p + 1), (taylor (ξ j) (nodePoly (L j) (h j))).coeff t * y j ^ t := by
    intro h hh j
    have hlt : (taylor (ξ j) (nodePoly (L j) (h j))).natDegree < p + 1 := by
      rw [natDegree_taylor, natDegree_nodePoly]
      have := ((mem_boxH.1 hh) j).1 (Finset.mem_univ j)
      omega
    rw [← eval_eq_sum_range' hlt, taylor_eval, nodeProd, eval_nodePoly]
    simp [add_comm]
  have heq : (∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) (ξ + y)) • C₀ h) =
      ∑ α ∈ box, (∏ i, y i ^ α i) • c α := by
    calc ∑ h ∈ boxH Finset.univ p, (∏ j, nodeProd L j (h j) (ξ + y)) • C₀ h
        = ∑ h ∈ boxH Finset.univ p, (∑ α ∈ box,
            ∏ j, ((taylor (ξ j) (nodePoly (L j) (h j))).coeff (α j) * y j ^ α j)) • C₀ h := by
          refine Finset.sum_congr rfl fun h hh => ?_
          rw [Finset.prod_congr rfl fun j _ => hN h hh j, Finset.prod_univ_sum]
      _ = ∑ α ∈ box, (∏ i, y i ^ α i) • c α := by
          simp_rw [Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.prod_mul_distrib, smul_smul, mul_comm]
  rw [heq]
  exact hasSum_sum_of_ne_finset_zero hfin

/-- A factor `(z i - ξ i) ^ m` kills the Taylor coefficients at `ξ` of order `< m` in the
`i`-th coordinate. -/
theorem taylorCoeff_pow_smul_eq_zero {G : (ι → ℂ) → V} {ξ : ι → ℂ} (hG : AnalyticAt ℂ G ξ)
    (i : ι) (m : ℕ) {κ : ι → ℕ} (hκ : κ i < m) :
    taylorCoeff (fun z => (z i - ξ i) ^ m • G z) ξ κ = 0 := by
  obtain ⟨ρ, hρ, hsum, hhs⟩ := exists_hasSum_of_analyticAt hG
  set d := taylorCoeff G ξ with hd
  set c : (ι → ℕ) → V := fun α => if m ≤ α i then d (α - Pi.single i m) else 0 with hc
  have hc_shift : ∀ β : ι → ℕ, c (β + Pi.single i m) = d β := by
    intro β
    simp only [hc, Pi.add_apply, Pi.single_eq_same, le_add_iff_nonneg_left, zero_le,
      ↓reduceIte]
    congr 1
    funext j
    simp
  have hc_van : ∀ α : ι → ℕ, α i < m → c α = 0 := fun α hα => by
    simp [hc, not_le.2 hα]
  have hsum_c : Summable fun α : ι → ℕ => ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i) := by
    have hinj : Function.Injective fun β : ι → ℕ => β + Pi.single i m := add_left_injective _
    have hzero : ∀ α ∉ Set.range fun β : ι → ℕ => β + Pi.single i m,
        ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i) = 0 := by
      intro α hα
      have hlt : ¬ m ≤ α i := fun hle => hα ⟨α - Pi.single i m, by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [Nat.sub_add_cancel hle]
        · simp [Pi.single_eq_of_ne hj]⟩
      simp [hc, hlt]
    rw [← hinj.summable_iff hzero]
    refine (hsum.mul_left ((ρ : ℝ) ^ m)).congr fun β => ?_
    simp only [Function.comp_apply, hc_shift, Pi.add_apply, Finset.sum_add_distrib,
      Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte, pow_add]
    ring
  have hhs_c : ∀ y : ι → ℂ, ‖y‖ < ρ → HasSum (fun α : ι → ℕ => (∏ j, y j ^ α j) • c α)
      ((fun z => (z i - ξ i) ^ m • G z) (ξ + y)) := by
    intro y hy
    have h1 : HasSum (fun β : ι → ℕ => (∏ j, y j ^ β j) • c (β + Pi.single i m))
        (G (ξ + y)) := by simpa [hc_shift] using hhs y hy
    simpa using hasSum_smul_shift_pow i m hc_van h1
  rw [taylorCoeff_eq_of_hasSum hρ hsum_c hhs_c κ]
  exact hc_van κ hκ

end MultiIndex
