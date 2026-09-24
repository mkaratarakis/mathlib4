/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Maximum modulus on a polydisc

For a finite index type `ι`, the `Pi` norm on `ι → ℂ` is the sup norm, so the closed ball
`Metric.closedBall 0 R` *is* the closed polydisc of polyradius `R`.  This file records the
maximum modulus principle in the form used for estimates on polydiscs: a bound valid wherever
one chosen coordinate has modulus exactly `R` already holds on the whole polydisc.

The proof fixes the other coordinates and applies the one-variable maximum modulus principle
along the remaining disc, so the bound propagates inwards one coordinate at a time.

## Main statements

* `Complex.norm_le_of_forall_norm_coord_eq`: the slicewise maximum modulus bound.
-/

@[expose] public section

open Metric

namespace Complex

variable {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The line through `z` in the direction of the `i`-th coordinate, as a function of that
coordinate; it is affine, hence analytic. -/
private lemma analyticAt_update [DecidableEq ι] (f : (ι → ℂ) → F) {R : ℝ}
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ f y) (z : ι → ℂ) (i : ι) {w : ℂ}
    (hw : ‖Function.update z i w‖ ≤ R) :
    AnalyticAt ℂ (fun v : ℂ => f (Function.update z i v)) w := by
  have haff : AnalyticAt ℂ (fun v : ℂ => Function.update z i v) w := by
    have hupd : (fun v : ℂ => Function.update z i v)
        = fun v : ℂ => z + (v - z i) • (Pi.single i 1 : ι → ℂ) := by
      funext v j
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    rw [hupd]
    exact analyticAt_const.add (((analyticAt_id).sub analyticAt_const).smul analyticAt_const)
  exact (hf _ hw).comp haff

/-- **Maximum modulus on a polydisc.**  If `f` is analytic on a neighbourhood of the closed
polydisc of polyradius `R` and `‖f z‖ ≤ C` at every point where the `i`-th coordinate has
modulus exactly `R`, then `‖f z‖ ≤ C` on the whole polydisc. -/
theorem norm_le_of_forall_norm_coord_eq {f : (ι → ℂ) → F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ f y) (i : ι) {C : ℝ}
    (hC : ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖y i‖ = R → ‖f y‖ ≤ C) :
    ∀ z : ι → ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ C := by
  classical
  intro z hz
  -- the values of `f` along the `i`-th coordinate line through `z`
  set g : ℂ → F := fun v => f (Function.update z i v) with hg
  have hmem : ∀ v : ℂ, ‖v‖ ≤ R → ‖Function.update z i v‖ ≤ R := by
    intro v hv
    refine (pi_norm_le_iff_of_nonneg hR.le).2 fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hv
    · rw [Function.update_of_ne hj]
      exact (norm_le_pi_norm z j).trans hz
  have hgan : ∀ v : ℂ, ‖v‖ ≤ R → AnalyticAt ℂ g v := fun v hv =>
    analyticAt_update f hf z i (hmem v hv)
  have hdiff : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    constructor
    · exact fun v hv =>
        ((hgan v (le_of_lt (by simpa using hv))).differentiableAt).differentiableWithinAt
    · refine ContinuousOn.mono (fun v hv => ?_) closure_ball_subset_closedBall
      exact ((hgan v (by simpa using hv)).continuousAt).continuousWithinAt
  have hbd : ∀ v ∈ frontier (ball (0 : ℂ) R), ‖g v‖ ≤ C := by
    intro v hv
    rw [frontier_ball _ hR.ne'] at hv
    have hvR : ‖v‖ = R := by simpa using hv
    refine hC _ (hmem v hvR.le) ?_
    simpa using hvR
  have hmem' : z i ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball _ hR.ne']
    simpa using (norm_le_pi_norm z i).trans hz
  simpa [hg] using norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff hbd hmem'

/-- If `f = z i ^ m • g` on a polydisc where `f` is bounded by `M`, then `g` is bounded by
`M / R ^ m` there.  This is the estimate accompanying the division step: dividing by a factor
of modulus `R` on the distinguished part of the boundary costs exactly `R ^ m`. -/
theorem norm_le_of_eq_pow_smul {f g : (ι → ℂ) → F} {R M : ℝ} (hR : 0 < R)
    (hg : ∀ y : ι → ℂ, ‖y‖ ≤ R → AnalyticAt ℂ g y) (i : ι) (m : ℕ)
    (heq : ∀ y : ι → ℂ, ‖y‖ ≤ R → f y = y i ^ m • g y)
    (hf : ∀ y : ι → ℂ, ‖y‖ ≤ R → ‖f y‖ ≤ M) :
    ∀ z : ι → ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M / R ^ m := by
  refine norm_le_of_forall_norm_coord_eq hR hg i fun y hy hyi => ?_
  have hpow : ‖y i ^ m‖ = R ^ m := by rw [norm_pow, hyi]
  have h1 : ‖f y‖ = R ^ m * ‖g y‖ := by rw [heq y hy, norm_smul, hpow]
  rw [le_div_iff₀ (by positivity)]
  calc ‖g y‖ * R ^ m = ‖f y‖ := by rw [h1]; ring
    _ ≤ M := hf y hy

/-!
### Products of linear factors

The polynomial `∏ ζ ∈ S, (z - ζ) ^ m` with all roots in the disc of radius `r` is small on
that disc and bounded below on a circle of radius `R > r`.  These are the two bounds a
Schwarz lemma with prescribed zeros trades against each other.
-/

/-- A product of linear factors with roots in the disc of radius `r` is bounded below on the
circle of radius `R`. -/
lemma norm_prod_sub_pow_ge {S : Finset ℂ} {r R : ℝ} (hrR : r ≤ R)
    (hS : ∀ ζ ∈ S, ‖ζ‖ ≤ r) (m : ℕ) {z : ℂ} (hz : ‖z‖ = R) :
    (R - r) ^ (m * S.card) ≤ ‖∏ ζ ∈ S, (z - ζ) ^ m‖ := by
  rw [norm_prod, pow_mul, ← Finset.prod_const]
  have hfac : ∀ ζ ∈ S, (R - r) ^ m ≤ ‖(z - ζ) ^ m‖ := by
    intro ζ hζ
    rw [norm_pow]
    refine pow_le_pow_left₀ (by linarith) ?_ m
    calc R - r ≤ ‖z‖ - ‖ζ‖ := by rw [hz]; linarith [hS ζ hζ]
      _ ≤ ‖z - ζ‖ := norm_sub_norm_le z ζ
  gcongr with ζ hζ
  exact hfac ζ hζ

/-- A product of linear factors with roots in the disc of radius `r` is bounded above on that
same disc. -/
lemma norm_prod_sub_pow_le {S : Finset ℂ} {r : ℝ}
    (hS : ∀ ζ ∈ S, ‖ζ‖ ≤ r) (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖∏ ζ ∈ S, (z - ζ) ^ m‖ ≤ (2 * r) ^ (m * S.card) := by
  rw [norm_prod, pow_mul, ← Finset.prod_const]
  have hfac : ∀ ζ ∈ S, ‖(z - ζ) ^ m‖ ≤ (2 * r) ^ m := by
    intro ζ hζ
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
    calc ‖z - ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le z ζ
      _ ≤ 2 * r := by linarith [hS ζ hζ]
  gcongr with ζ hζ
  exact hfac ζ hζ

end Complex
