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
basic properties (`NormedSpace.exp_add_of_mem_ball`,
`NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos`, …) hold inside the ball of convergence of
`NormedSpace.expSeries`. Over `ℂ_[p]` that ball is not
all of `ℂ_[p]`; this file shows that it contains the disc of radius `p ^ (-1 / (p - 1))`.

The estimate is `‖1 / n!‖ * p ^ (-n / (p - 1)) ≤ 1`, which is Legendre's bound
`(p - 1) * v_p(n!) ≤ n` (`sub_one_mul_padicValNat_factorial`).

## Main statements

* `PadicComplex.norm_natCast_factorial`: `‖n!‖ = p ^ (-v_p(n!))` in `ℂ_[p]`.
* `PadicComplex.norm_factorial_inv_mul_pow_le`: `‖1 / n!‖ * ρ ^ n ≤ 1` for `ρ = p ^ (-1 / (p - 1))`.
* `PadicComplex.le_radius_expSeries`: the exponential series converges on the disc of radius `ρ`.
* `PadicComplex.exp_add`: `exp (x + y) = exp x * exp y` on that disc.
* `PadicComplex.norm_exp_sub_one`: `‖exp x - 1‖ = ‖x‖` on that disc, so `exp` is injective there
  (`PadicComplex.exp_injOn`) and takes values of norm one.
* `PadicComplex.exp_nsmul`, `PadicComplex.exp_sum`: `exp (n • x) = exp x ^ n` and
  `exp (∑ x i) = ∏ exp (x i)` on that disc.
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

/-- `‖x ^ n / n!‖ ≤ ‖x‖ * (‖x‖ * p ^ (1 / (p - 1))) ^ (n - 1)` for `n ≥ 1`: Legendre's bound in the
form used for the isometry property of `exp`. -/
theorem norm_pow_div_factorial_le {x : ℂ_[p]} {n : ℕ} (hn : 1 ≤ n) :
    ‖x ^ n / (n ! : ℂ_[p])‖ ≤ ‖x‖ * (‖x‖ * (p : ℝ) ^ ((p : ℝ) - 1)⁻¹) ^ (n - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : (0 : ℝ) < p - 1 := by linarith
  set v := padicValNat p n ! with hv
  -- Legendre: `(p - 1) * v ≤ n - 1`
  have hleg : ((p : ℝ) - 1) * v ≤ (n - 1 : ℕ) := by
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) (by omega : n ≠ 0)
    have h' : (p - 1) * v ≤ n - 1 := by rw [hv]; omega
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
    have := (Nat.cast_le (α := ℝ)).mpr h'
    rwa [Nat.cast_mul, hcast] at this
  have hfac : ‖((n ! : ℕ) : ℂ_[p])⁻¹‖ ≤ ((p : ℝ) ^ ((p : ℝ) - 1)⁻¹) ^ (n - 1) := by
    rw [norm_inv, norm_natCast_factorial, zpow_neg, inv_inv, zpow_natCast,
      ← Real.rpow_natCast ((p : ℝ) ^ _) (n - 1), ← Real.rpow_mul hp0.le,
      ← Real.rpow_natCast (p : ℝ) v]
    refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
    rw [inv_mul_eq_div, le_div_iff₀ hpm, mul_comm]
    exact hleg
  calc ‖x ^ n / (n ! : ℂ_[p])‖ = ‖x‖ ^ n * ‖((n ! : ℕ) : ℂ_[p])⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul, norm_pow]
    _ ≤ ‖x‖ ^ n * ((p : ℝ) ^ ((p : ℝ) - 1)⁻¹) ^ (n - 1) := by gcongr
    _ = ‖x‖ * (‖x‖ * (p : ℝ) ^ ((p : ℝ) - 1)⁻¹) ^ (n - 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [Nat.add_sub_cancel, mul_pow, ← mul_assoc, pow_succ ‖x‖ k, mul_comm (‖x‖ ^ k) ‖x‖]

/-- **The `p`-adic exponential is an isometry near `0`**: `‖exp x - 1‖ = ‖x‖` on the disc of
radius `p ^ (-1 / (p - 1))`. -/
theorem norm_exp_sub_one {x : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖exp x - 1‖ = ‖x‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  set q := ‖x‖ * (p : ℝ) ^ ((p : ℝ) - 1)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have hpos : 0 < (p : ℝ) ^ ((p : ℝ) - 1)⁻¹ := by positivity
    rw [hq, ← lt_div_iff₀ hpos, one_div, ← Real.rpow_neg hp0.le]
    exact hx
  -- the tail `∑_{n ≥ 2} x ^ n / n!`
  have hsum := expSeries_div_hasSum_exp_of_mem_ball ℂ_[p] x (mem_eball_radius_expSeries hx)
  have htail : HasSum (fun n => x ^ (n + 2) / ((n + 2) ! : ℂ_[p])) (exp x - (1 + x)) := by
    have := (hasSum_nat_add_iff' (f := fun n => x ^ n / (n ! : ℂ_[p])) 2).mpr hsum
    simpa [Finset.sum_range_succ] using this
  have hbound : ‖exp x - (1 + x)‖ ≤ ‖x‖ * q := by
    rw [← htail.tsum_eq]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n => ?_
    calc ‖x ^ (n + 2) / ((n + 2) ! : ℂ_[p])‖ ≤ ‖x‖ * q ^ (n + 2 - 1) :=
          norm_pow_div_factorial_le (by omega)
      _ ≤ ‖x‖ * q := by
          gcongr
          exact pow_le_of_le_one hq0 hq1.le (by omega)
  have hlt : ‖exp x - (1 + x)‖ < ‖x‖ :=
    hbound.trans_lt (mul_lt_of_lt_one_right (norm_pos_iff.mpr hx0) hq1)
  have hne : ‖x‖ ≠ ‖exp x - (1 + x)‖ := hlt.ne'
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [max_eq_left hlt.le] at h
  rw [← h]
  congr 1
  ring

/-- `exp` takes values of norm one on the disc of radius `p ^ (-1 / (p - 1))`. -/
theorem norm_exp {x : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) : ‖exp x‖ = 1 := by
  have hρ : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.out.one_le)
      (neg_nonpos.mpr (inv_nonneg.mpr (by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
        linarith)))
  have h1 : ‖exp x - 1‖ < ‖(1 : ℂ_[p])‖ := by
    rw [norm_exp_sub_one hx, norm_one]; exact hx.trans_le hρ
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
  rw [sub_add_cancel, max_eq_right h1.le, norm_one] at this
  exact this

/-- **`exp` is injective on the disc of radius `p ^ (-1 / (p - 1))`.** -/
theorem exp_injOn : Set.InjOn (exp : ℂ_[p] → ℂ_[p])
    {x | ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)} := by
  intro x hx y hy hxy
  have hneg : ‖-y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by rwa [norm_neg]
  have hdiff : ‖x + -y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    (IsUltrametricDist.norm_add_le_max x (-y)).trans_lt (max_lt hx hneg)
  have hexp : exp (x + -y) = 1 := by
    rw [exp_add hx hneg, hxy, ← exp_add hy hneg, add_neg_cancel, exp_zero]
  have := norm_exp_sub_one hdiff
  rw [hexp, sub_self, norm_zero] at this
  rw [← sub_eq_zero, sub_eq_add_neg]
  exact norm_eq_zero.mp this.symm

/-- The disc of radius `p ^ (-1 / (p - 1))` is closed under addition. -/
theorem norm_add_lt_expRadius {x y : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) : ‖x + y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

/-- The disc of radius `p ^ (-1 / (p - 1))` is closed under multiplication by naturals. -/
theorem norm_nsmul_lt_expRadius {x : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    ‖n • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  rw [nsmul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ n)).trans_lt
    hx

/-- `exp (n • x) = exp x ^ n` on the disc of radius `p ^ (-1 / (p - 1))`. -/
theorem exp_nsmul {x : ℂ_[p]} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    exp (n • x) = exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, exp_add (norm_nsmul_lt_expRadius hx n) hx, ih, pow_succ]

/-- `exp (∑ x i) = ∏ exp (x i)` on the disc of radius `p ^ (-1 / (p - 1))`. -/
theorem exp_sum {ι : Type*} (s : Finset ι) {x : ι → ℂ_[p]}
    (hx : ∀ i ∈ s, ‖x i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    exp (∑ i ∈ s, x i) = ∏ i ∈ s, exp (x i) := by
  classical
  have hρ : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ‖x i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := fun i hi =>
      hx i (Finset.mem_insert_of_mem hi)
    have hsum : ‖∑ i ∈ s, x i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simpa using hρ
      obtain ⟨j, hj, hjmax⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne x
      exact hjmax.trans_lt (hs j hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      exp_add (hx a (Finset.mem_insert_self a s)) hsum, ih hs]

end PadicComplex
