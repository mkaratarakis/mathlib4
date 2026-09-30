/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# Reverse Young and reverse Hölder inequalities

For `0 < p < 1`, the exponent `q` with `p⁻¹ + q⁻¹ = 1` is negative, and the inequalities of Young
and Hölder hold in the reverse direction.

## Main results

* `Real.young_inequality_of_lt_one`: the reverse Young inequality
  `a / p + b / q ≤ a ^ (1 / p) * b ^ (1 / q)` for `a ≥ 0`, `b > 0`.
* `Real.Lp_mul_Lq_le_inner_of_lt_one`: the reverse Hölder inequality
  `(∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) ≤ ∑ i ∈ s, f i * g i`
  for `f i ≥ 0`, `g i > 0`.

## References

* [A. Dujella, J. Jakšetić and J. Pečarić, *Fibonacci numbers and Hölder inequality*]
  [dujella_jaksetic_pecaric]
-/

public section

open Finset

namespace Real

variable {ι : Type*} {p q : ℝ}

/-- If `0 < p < 1` and `p⁻¹ + q⁻¹ = 1`, then the conjugate exponent `q` is negative. -/
lemma neg_of_inv_add_inv_eq_one (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) : q < 0 :=
  inv_lt_zero.1 (by linarith [(one_lt_inv₀ hp0).2 hp1])

/-- **Reverse Young inequality**: for `0 < p < 1`, `p⁻¹ + q⁻¹ = 1`, `0 ≤ a` and `0 < b`,
`a / p + b / q ≤ a ^ (1 / p) * b ^ (1 / q)`. Equivalently, `x ^ p / p + y ^ q / q ≤ x * y` for
`x ≥ 0` and `y > 0`, the reverse of `Real.young_inequality_of_nonneg`. -/
theorem young_inequality_of_lt_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) : a / p + b / q ≤ a ^ (1 / p) * b ^ (1 / q) := by
  have hq : q⁻¹ = 1 - p⁻¹ := by linarith
  have h := geom_mean_le_arith_mean2_weighted hp0.le (sub_nonneg.2 hp1.le)
    (by positivity : 0 ≤ a ^ (1 / p) * b ^ (1 / q)) hb.le (add_sub_cancel p 1)
  have hXp : (a ^ (1 / p) * b ^ (1 / q)) ^ p * b ^ (1 - p) = a := by
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul ha, ← rpow_mul hb.le, mul_assoc,
      ← rpow_add hb, one_div_mul_cancel hp0.ne', rpow_one, one_div, hq,
      show (1 - p⁻¹) * p + (1 - p) = 0 by field_simp; ring, rpow_zero, mul_one]
  rw [hXp] at h
  rw [div_eq_mul_inv b q, hq, show a / p + b * (1 - p⁻¹) = (a + b * (p - 1)) / p by field_simp,
    div_le_iff₀ hp0]
  linarith

/-- **Reverse Hölder inequality**: for `0 < p < 1` and `p⁻¹ + q⁻¹ = 1` (so that `q < 0`), and for
`f i ≥ 0` and `g i > 0`,
`(∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) ≤ ∑ i ∈ s, f i * g i`. -/
theorem Lp_mul_Lq_le_inner_of_lt_one (s : Finset ι) (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) ≤ ∑ i ∈ s, f i * g i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hp0.ne']
  have hq : 1 / q = 1 - 1 / p := by rw [one_div, one_div]; linarith
  have hqp : -p * (1 / (1 - p)) = q := by
    have : 1 - p ≠ 0 := sub_ne_zero.2 hp1.ne'
    have : q ≠ 0 := (neg_of_inv_add_inv_eq_one hp0 hp1 hpq).ne
    field_simp at hpq ⊢
    linarith
  have hfg : ∀ i ∈ s, 0 ≤ f i * g i := fun i hi ↦ mul_nonneg (hf i hi) (hg i hi).le
  have H := inner_le_Lp_mul_Lq_of_nonneg s
    (holderConjugate_one_div hp0 (sub_pos.2 hp1) (add_sub_cancel p 1))
    (f := fun i ↦ (f i * g i) ^ p) (g := fun i ↦ g i ^ (-p))
    (fun i hi ↦ rpow_nonneg (hfg i hi) _) (fun i hi ↦ (rpow_pos_of_pos (hg i hi) _).le)
  have e1 : ∑ i ∈ s, (f i * g i) ^ p * g i ^ (-p) = ∑ i ∈ s, f i ^ p :=
    sum_congr rfl fun i hi ↦ by
      rw [mul_rpow (hf i hi) (hg i hi).le, mul_assoc, ← rpow_add (hg i hi), add_neg_cancel,
        rpow_zero, mul_one]
  have e2 : ∑ i ∈ s, ((f i * g i) ^ p) ^ (1 / p) = ∑ i ∈ s, f i * g i :=
    sum_congr rfl fun i hi ↦ by rw [one_div, rpow_rpow_inv (hfg i hi) hp0.ne']
  have e3 : ∑ i ∈ s, (g i ^ (-p)) ^ (1 / (1 - p)) = ∑ i ∈ s, g i ^ q :=
    sum_congr rfl fun i hi ↦ by rw [← rpow_mul (hg i hi).le, hqp]
  simp only [one_div_one_div] at H
  rw [e1, e2, e3] at H
  have hF : 0 ≤ ∑ i ∈ s, f i * g i := sum_nonneg hfg
  have hG : 0 < ∑ i ∈ s, g i ^ q := sum_pos (fun i hi ↦ rpow_pos_of_pos (hg i hi) _) hs
  calc (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)
      ≤ ((∑ i ∈ s, f i * g i) ^ p * (∑ i ∈ s, g i ^ q) ^ (1 - p)) ^ (1 / p) *
          (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
        gcongr
        exact sum_nonneg fun i hi ↦ rpow_nonneg (hf i hi) _
    _ = (∑ i ∈ s, f i * g i) * ((∑ i ∈ s, g i ^ q) ^ ((1 - p) * (1 / p)) *
          (∑ i ∈ s, g i ^ q) ^ (1 / q)) := by
        rw [mul_rpow (by positivity) (by positivity), ← rpow_mul hF, ← rpow_mul hG.le,
          mul_one_div_cancel hp0.ne', rpow_one, mul_assoc]
    _ = ∑ i ∈ s, f i * g i := by
        rw [← rpow_add hG, hq, show (1 - p) * (1 / p) + (1 - 1 / p) = 0 by field_simp; ring,
          rpow_zero, mul_one]

end Real
