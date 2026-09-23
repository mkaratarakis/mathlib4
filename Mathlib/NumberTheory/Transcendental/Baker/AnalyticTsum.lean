/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Analyticity of an infinite sum of analytic functions

`Mathlib/Analysis/Analytic/Constructions.lean` shows that analyticity is preserved by
*finite* sums (`AnalyticAt.add`).  This file supplies the countable version: a sum
`∑' n, g n` of functions having power series `p n` on a common ball is analytic there, with
power series `fun k => ∑' n, p n k`, provided the double family of coefficient norms is
summable.

This is the missing bridge from a multi-indexed power series to `AnalyticAt`: a series in
several variables is a sum over multi-indices of monomials, each of which is analytic, so
this lemma turns the series into an honest `FormalMultilinearSeries`.

Everything is stated over an arbitrary nontrivially normed field and arbitrary normed
spaces; no finite-dimensionality is used.

This file belongs in `Mathlib/Analysis/Analytic/Constructions.lean`.

## Main statements

* `hasFPowerSeriesOnBall_tsum`: the power series of a normally convergent sum.
* `analyticAt_tsum`: the corresponding `AnalyticAt` statement.
-/

@[expose] public section

open scoped NNReal ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Evaluation of a continuous multilinear map at a fixed point, as an additive monoid
homomorphism; used to push `HasSum` through evaluation. -/
private def evalAddHom (k : ℕ) (m : Fin k → E) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F →+ F where
  toFun f := f m
  map_zero' := rfl
  map_add' _ _ := rfl

/-- If each `g n` has power series `p n` on the ball of radius `r` about `x`, and the
double family `‖p n k‖ * r ^ k` is summable, then `∑' n, g n` has power series
`fun k => ∑' n, p n k` on that ball. -/
theorem hasFPowerSeriesOnBall_tsum {ι : Type*} {g : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0} (hr : 0 < r)
    (hg : ∀ n, HasFPowerSeriesOnBall (g n) (p n) x r)
    (hsum : Summable fun ki : ℕ × ι => ‖p ki.2 ki.1‖ * (r : ℝ) ^ ki.1) :
    HasFPowerSeriesOnBall (fun z => ∑' n, g n z) (fun k => ∑' n, p n k) x r := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  -- Summability of the coefficient norms for each fixed degree.
  have hfibnorm : ∀ k, Summable fun n : ι => ‖p n k‖ := by
    intro k
    have h1 : Summable fun n : ι => ‖p n k‖ * (r : ℝ) ^ k :=
      hsum.comp_injective (i := fun n : ι => (k, n)) fun a b h => by simpa using h
    have h2 := h1.mul_right ((r : ℝ) ^ k)⁻¹
    simpa [mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hrR.ne')] using h2
  have hfib : ∀ k, Summable fun n : ι => p n k := fun k => (hfibnorm k).of_norm
  set q : FormalMultilinearSeries 𝕜 E F := fun k => ∑' n, p n k with hqdef
  have hqnorm : ∀ k, ‖q k‖ ≤ ∑' n, ‖p n k‖ := fun k => norm_tsum_le_tsum_norm (hfibnorm k)
  -- The radius of the summed series is at least `r`.
  have hnn : (0 : ℕ × ι → ℝ) ≤ fun ki => ‖p ki.2 ki.1‖ * (r : ℝ) ^ ki.1 := by
    intro ki; positivity
  have houter : Summable fun k : ℕ => ∑' n : ι, ‖p n k‖ * (r : ℝ) ^ k :=
    ((summable_prod_of_nonneg hnn).1 hsum).2
  have hradius : (r : ℝ≥0∞) ≤ q.radius := by
    refine q.le_radius_of_summable ?_
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) houter
    calc ‖q k‖ * (r : ℝ) ^ k ≤ (∑' n, ‖p n k‖) * (r : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (hqnorm k) (by positivity)
      _ = ∑' n, ‖p n k‖ * (r : ℝ) ^ k := by rw [tsum_mul_right]
  refine ⟨hradius, by exact_mod_cast hr, fun {y} hy => ?_⟩
  have hynorm : ‖y‖ < (r : ℝ) := by
    have h : ‖y‖ₑ < (r : ℝ≥0∞) := mem_eball_zero_iff.1 hy
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at h
    exact_mod_cast h
  -- The doubly indexed family of terms is summable.
  have hdbl : Summable fun ki : ℕ × ι => p ki.2 ki.1 fun _ => y := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ki => ?_) hsum)
    calc ‖p ki.2 ki.1 fun _ => y‖ ≤ ‖p ki.2 ki.1‖ * ∏ _i : Fin ki.1, ‖y‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖p ki.2 ki.1‖ * ‖y‖ ^ ki.1 := by simp
      _ ≤ ‖p ki.2 ki.1‖ * (r : ℝ) ^ ki.1 := by gcongr
  set S := ∑' ki : ℕ × ι, p ki.2 ki.1 fun _ => y with hSdef
  have hSsum : HasSum (fun ki : ℕ × ι => p ki.2 ki.1 fun _ => y) S := hdbl.hasSum
  -- Summing first over `ι` gives the coefficients of `q`.
  have hcoeff : ∀ k, HasSum (fun n : ι => p n k fun _ => y) (q k fun _ => y) := by
    intro k
    have := (hfib k).hasSum.map (evalAddHom k fun _ => y) (by exact continuous_eval_const _)
    simpa [evalAddHom, hqdef, Function.comp_def] using this
  have hgoal : HasSum (fun k : ℕ => q k fun _ => y) S := hSsum.prod_fiberwise hcoeff
  -- Summing first over `ℕ` gives the values of the `g n`.
  have hswap : HasSum (fun nk : ι × ℕ => p nk.1 nk.2 fun _ => y) S := by
    simpa [Function.comp_def] using (Equiv.prodComm ι ℕ).hasSum_iff.mpr hSsum
  have hvals : HasSum (fun n : ι => g n (x + y)) S :=
    hswap.prod_fiberwise fun n => (hg n).hasSum hy
  rwa [hvals.tsum_eq]

/-- Analyticity is preserved by normally convergent infinite sums. -/
theorem analyticAt_tsum {ι : Type*} {g : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0} (hr : 0 < r)
    (hg : ∀ n, HasFPowerSeriesOnBall (g n) (p n) x r)
    (hsum : Summable fun ki : ℕ × ι => ‖p ki.2 ki.1‖ * (r : ℝ) ^ ki.1) :
    AnalyticAt 𝕜 (fun z => ∑' n, g n z) x :=
  (hasFPowerSeriesOnBall_tsum hr hg hsum).analyticAt
