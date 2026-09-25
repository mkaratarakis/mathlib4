/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The `p`-adic exponential on its disc of convergence

Mathlib's `NormedSpace.exp` is defined by its series in any complete normed algebra, and its
basic properties (`NormedSpace.exp_add_of_mem_ball`, `NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos`,
…) hold inside the ball of convergence of `NormedSpace.expSeries`. Over `ℂ_[p]` that ball is not
all of `ℂ_[p]`; this file shows that it contains the disc of radius `p ^ (-1 / (p - 1))`.

The estimate is `‖1 / n!‖ * p ^ (-n / (p - 1)) ≤ 1`, which is Legendre's bound
`(p - 1) * v_p(n!) ≤ n` (`sub_one_mul_padicValNat_factorial`).

## Main statements

* `PadicComplex.norm_natCast_factorial`: `‖n!‖ = p ^ (-v_p(n!))` in `ℂ_[p]`.
* `PadicComplex.norm_factorial_inv_mul_pow_le`: `‖1 / n!‖ * ρ ^ n ≤ 1` for `ρ = p ^ (-1 / (p - 1))`.
* `PadicComplex.le_radius_expSeries`: the exponential series converges on the disc of radius `ρ`.
* `PadicComplex.exp_add`: `exp (x + y) = exp x * exp y` on that disc.
-/

@[expose] public section

open Nat NormedSpace

namespace PadicComplex

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `p`-adic norm of `n!`. -/
theorem norm_natCast_factorial (n : ℕ) :
    ‖((n ! : ℕ) : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n ! : ℤ)) := by
  have hcast : (((n ! : ℕ) : ℚ_[p]) : ℂ_[p]) = ((n ! : ℕ) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_eq, map_natCast]
  rw [← hcast, norm_extends',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast (Nat.factorial_ne_zero n)),
    Padic.valuation_natCast]

/-- **Legendre's bound in norm form.** With `ρ = p ^ (-1 / (p - 1))`, `‖1 / n!‖ * ρ ^ n ≤ 1`. -/
theorem norm_factorial_inv_mul_pow_le (n : ℕ) :
    ‖((n ! : ℕ) : ℂ_[p])⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ n ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : (0 : ℝ) < p - 1 := by linarith
  set v := padicValNat p n ! with hv
  -- Legendre: `(p - 1) * v ≤ n`
  have hleg : ((p : ℝ) - 1) * v ≤ n := by
    have h := sub_one_mul_padicValNat_factorial (p := p) n
    have h' : (p - 1) * v ≤ n := by rw [hv, h]; exact Nat.sub_le _ _
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
    have := (Nat.cast_le (α := ℝ)).mpr h'
    rwa [Nat.cast_mul, hcast] at this
  rw [norm_inv, norm_natCast_factorial, zpow_neg, inv_inv, zpow_natCast,
    ← Real.rpow_natCast ((p : ℝ) ^ _) n, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast (p : ℝ) v,
    ← Real.rpow_add hp0]
  refine Real.rpow_le_one_of_one_le_of_nonpos hp1.le ?_
  have : (v : ℝ) ≤ n / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ hpm, mul_comm]; exact hleg
  have hdiv : -((p : ℝ) - 1)⁻¹ * n = -(n / ((p : ℝ) - 1)) := by ring
  rw [hdiv]
  linarith

/-- **The `p`-adic exponential converges on the disc of radius `p ^ (-1 / (p - 1))`.** -/
theorem le_radius_expSeries :
    ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ≤ (expSeries ℂ_[p] ℂ_[p]).radius := by
  have hρ : 0 ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by positivity
  rw [ENNReal.ofReal]
  refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun n => ?_
  rw [Real.coe_toNNReal _ hρ, expSeries_eq_ofScalars,
    FormalMultilinearSeries.ofScalars_norm_eq_mul, ContinuousMultilinearMap.norm_mkPiAlgebraFin,
    mul_one]
  exact norm_factorial_inv_mul_pow_le n

/-- Points of the disc of radius `p ^ (-1 / (p - 1))` lie in the ball of convergence of the
exponential series. -/
theorem mem_eball_radius_expSeries {x : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    x ∈ Metric.eball (0 : ℂ_[p]) (expSeries ℂ_[p] ℂ_[p]).radius := by
  refine Metric.eball_subset_eball le_radius_expSeries ?_
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal,
    coe_nnnorm]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hx

/-- **The functional equation of the `p`-adic exponential** on the disc of radius
`p ^ (-1 / (p - 1))`. -/
theorem exp_add {x y : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) : exp (x + y) = exp x * exp y :=
  exp_add_of_mem_ball (mem_eball_radius_expSeries hx) (mem_eball_radius_expSeries hy)

end PadicComplex
