/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.MultiIndex

/-!
# Taylor coefficients at a point

`MultiIndex.taylorCoeff f x α` is the coefficient of `(z - x) ^ α` in the expansion of `f` about
`x`, that is `D^α f (x) / α!`, and `0` where `f` is not analytic at `x`.  It is defined from any
power series of `f` at `x`; the choice does not matter
(`MultiIndex.coeff_eq_of_hasFPowerSeriesAt`).  Working with these coefficients rather than with
partial derivatives avoids a multi-index derivative API, which Mathlib does not have.

## Main statements

* `MultiIndex.taylorCoeff_eq`: the Taylor coefficients are the multi-index coefficients of any
  power series of `f` at the point.
* `MultiIndex.taylorCoeff_eq_of_hasSum`: the coefficients of any normally convergent expansion
  of `f` about the point are its Taylor coefficients.
* `MultiIndex.exists_hasSum_of_analyticAt`: an analytic function is the sum of its Taylor
  expansion on some polydisc.
-/

@[expose] public section

open Metric Function Filter Topology
open scoped NNReal ENNReal

namespace MultiIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

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
end MultiIndex
