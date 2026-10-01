/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Linarith

/-!
# The Lah–Ribarič inequality

Jensen's inequality bounds the values of a convex function `f` at a weighted mean from above by the
weighted mean of its values. The **Lah–Ribarič inequality** is a converse: if `f` is convex on
`[m, M]`, then the weighted mean of the values `f (r i)` at points `r i ∈ [m, M]` is at most the
value at the weighted mean of the `r i` of the chord of `f` over `[m, M]`.

## Main results

* `ConvexOn.lah_ribaric`: over a linearly ordered field `𝕜`, if `f : 𝕜 → 𝕜` is convex on
  `[m, M]`, `c i ≥ 0` and `r i ∈ [m, M]` for `i ∈ s`, then
  `(M - m) * ∑ i ∈ s, c i * f (r i) + (m * f M - M * f m) * ∑ i ∈ s, c i ≤
  (f M - f m) * ∑ i ∈ s, c i * r i`.
* `ConcaveOn.lah_ribaric`: the reverse inequality for `f` concave on `[m, M]`.

## References

* [P. Lah and M. Ribarič, *Converse of Jensen's inequality for convex functions*]
  [lah_ribaric_1973]
-/

public section

open Finset

variable {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (s : Finset ι)
  {f : 𝕜 → 𝕜} {c r : ι → 𝕜} {m M : 𝕜}

/-- **Lah–Ribarič inequality**: if `f` is convex on `[m, M]`, `c i ≥ 0` and `r i ∈ [m, M]`, then
the weighted sum of the values `f (r i)` lies below the chord of `f` over `[m, M]`:
`(M - m) * ∑ i ∈ s, c i * f (r i) + (m * f M - M * f m) * ∑ i ∈ s, c i ≤
(f M - f m) * ∑ i ∈ s, c i * r i`. -/
theorem ConvexOn.lah_ribaric (hf : ConvexOn 𝕜 (Set.Icc m M) f) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc m M) :
    (M - m) * ∑ i ∈ s, c i * f (r i) + (m * f M - M * f m) * ∑ i ∈ s, c i ≤
      (f M - f m) * ∑ i ∈ s, c i * r i := by
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  obtain ⟨hmr, hrM⟩ := hr i hi
  have hchord : (M - m) * f (r i) ≤ (M - r i) * f m + (r i - m) * f M := by
    obtain hmr | hmr := hmr.eq_or_lt
    · simp [← hmr]
    obtain hrM | hrM := hrM.eq_or_lt
    · simp [hrM]
    have hmM := (hmr.trans hrM).le
    exact hf.secant_mono_aux1 ⟨le_rfl, hmM⟩ ⟨hmM, le_rfl⟩ hmr hrM
  have := mul_le_mul_of_nonneg_left hchord (hc i hi)
  linarith

/-- **Lah–Ribarič inequality** for concave functions: if `f` is concave on `[m, M]`, `c i ≥ 0`
and `r i ∈ [m, M]`, then the weighted sum of the values `f (r i)` lies above the chord of `f` over
`[m, M]`: `(f M - f m) * ∑ i ∈ s, c i * r i ≤
(M - m) * ∑ i ∈ s, c i * f (r i) + (m * f M - M * f m) * ∑ i ∈ s, c i`. -/
theorem ConcaveOn.lah_ribaric (hf : ConcaveOn 𝕜 (Set.Icc m M) f) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc m M) :
    (f M - f m) * ∑ i ∈ s, c i * r i ≤
      (M - m) * ∑ i ∈ s, c i * f (r i) + (m * f M - M * f m) * ∑ i ∈ s, c i := by
  have := hf.neg.lah_ribaric s hc hr
  simp only [Pi.neg_apply, mul_neg, sum_neg_distrib] at this
  linarith
