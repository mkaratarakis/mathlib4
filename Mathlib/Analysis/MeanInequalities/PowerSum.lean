/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.MeanInequalities.Reverse
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Inequalities between weighted power sums

For weights `w i` and nonnegative reals `x i`, `i ∈ s`, write `S γ = ∑ i ∈ s, w i * x i ^ γ` for
the weighted power sum of exponent `γ` and `W = ∑ i ∈ s, w i` for the total weight. This file
compares these quantities for different exponents.

## Main results

* `Real.sum_rpow_le_rpow_sum`, `Real.rpow_sum_le_sum_rpow`: `∑ y i ^ γ ≤ (∑ y i) ^ γ` for
  `γ ≥ 1`, and the reverse inequality for `0 ≤ γ ≤ 1`, for nonnegative `y i`.
* `Real.sum_mul_rpow_le_of_one_lt`, `Real.le_sum_mul_rpow_of_lt_one`: Hölder's inequality
  `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` for `α = u / p + v / q` and conjugate exponents `p`, `q`
  with `p > 1`, and its reverse for `0 < p < 1`.
* `Real.rpow_mean_le_of_le`, `Real.le_rpow_mean_of_le`: the power mean inequality
  `W ^ (1 - α / β) * S β ^ (α / β) ≤ S α` for `0 < β ≤ α`, and its reverse for `0 < α ≤ β`.
* `Real.sum_le_rpow_mean_of_one_le`, `Real.rpow_mean_le_sum_of_one_le`: comparison of
  `S β` with `W ^ (1 - α / β) * S β ^ (α / β)` when `1 ≤ x i`.
* `Real.sum_rpow_le_rpow_of_le`, `Real.sum_rpow_rpow_le_of_le`, `Real.rpow_le_sum_rpow_of_le`:
  monotonicity of the weighted `ℓ^γ` norms `S γ ^ (1 / γ)` when `1 ≤ w i`.

Dujella, Jakšetić and Pečarić chain these inequalities in the unweighted case `w = 1` (their
Theorems 6 and 7).

## References

* [A. Dujella, J. Jakšetić and J. Pečarić, *Fibonacci numbers and Hölder inequality*]
  [dujella_jaksetic_pecaric]
-/

public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-- `(x ^ b) ^ (a / b) = x ^ a` for `0 ≤ x` and `b ≠ 0`. -/
lemma rpow_rpow_div {x : ℝ} (a : ℝ) {b : ℝ} (hx : 0 ≤ x) (hb : b ≠ 0) :
    (x ^ b) ^ (a / b) = x ^ a := by
  rw [← rpow_mul hx, mul_div_cancel₀ a hb]

/-! ### Superadditivity and subadditivity of `y ↦ y ^ γ` on finite sums -/

/-- For `γ ≥ 1` and `y i ≥ 0`, `∑ i ∈ s, y i ^ γ ≤ (∑ i ∈ s, y i) ^ γ`. -/
theorem sum_rpow_le_rpow_sum {γ : ℝ} (hγ : 1 ≤ γ) {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, y i ^ γ ≤ (∑ i ∈ s, y i) ^ γ := by
  induction s using Finset.cons_induction with
  | empty => simp [zero_rpow (by linarith : γ ≠ 0)]
  | cons a s ha ih =>
    rw [sum_cons, sum_cons]
    have hy' : ∀ i ∈ s, 0 ≤ y i := fun i hi ↦ hy i (mem_cons_of_mem hi)
    grw [ih hy']
    exact add_rpow_le_rpow_add (hy a (mem_cons_self a s)) (sum_nonneg hy') hγ

/-- For `0 ≤ γ ≤ 1`, `y i ≥ 0` and nonempty `s`, `(∑ i ∈ s, y i) ^ γ ≤ ∑ i ∈ s, y i ^ γ`. -/
theorem rpow_sum_le_sum_rpow {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : s.Nonempty)
    {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, y i) ^ γ ≤ ∑ i ∈ s, y i ^ γ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [sum_cons, sum_cons]
    have hy' : ∀ i ∈ s, 0 ≤ y i := fun i hi ↦ hy i (mem_cons_of_mem hi)
    grw [← ih hy']
    exact rpow_add_le_add_rpow (hy a (mem_cons_self a s)) (sum_nonneg hy') hγ0 hγ1

/-- For `γ ≥ 1`, `w i ≥ 1` and `y i ≥ 0`,
`∑ i ∈ s, w i * y i ^ γ ≤ (∑ i ∈ s, w i * y i) ^ γ`. -/
theorem sum_mul_rpow_le_rpow_sum_mul {γ : ℝ} (hγ : 1 ≤ γ) {y : ι → ℝ}
    (hw : ∀ i ∈ s, 1 ≤ w i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, w i * y i ^ γ ≤ (∑ i ∈ s, w i * y i) ^ γ := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi ↦ zero_le_one.trans (hw i hi)
  calc ∑ i ∈ s, w i * y i ^ γ ≤ ∑ i ∈ s, (w i * y i) ^ γ := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [mul_rpow (hw0 i hi) (hy i hi)]
        gcongr
        · exact rpow_nonneg (hy i hi) _
        · simpa using rpow_le_rpow_of_exponent_le (hw i hi) hγ
    _ ≤ _ := sum_rpow_le_rpow_sum s hγ fun i hi ↦ mul_nonneg (hw0 i hi) (hy i hi)

/-- For `0 ≤ γ ≤ 1`, `w i ≥ 1`, `y i ≥ 0` and nonempty `s`,
`(∑ i ∈ s, w i * y i) ^ γ ≤ ∑ i ∈ s, w i * y i ^ γ`. -/
theorem rpow_sum_mul_le_sum_mul_rpow {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hs : s.Nonempty) {y : ι → ℝ} (hw : ∀ i ∈ s, 1 ≤ w i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, w i * y i) ^ γ ≤ ∑ i ∈ s, w i * y i ^ γ := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi ↦ zero_le_one.trans (hw i hi)
  calc _ ≤ ∑ i ∈ s, (w i * y i) ^ γ :=
        rpow_sum_le_sum_rpow s hγ0 hγ1 hs fun i hi ↦ mul_nonneg (hw0 i hi) (hy i hi)
    _ ≤ _ := sum_le_sum fun i hi ↦ by
        rw [mul_rpow (hw0 i hi) (hy i hi)]
        gcongr
        · exact rpow_nonneg (hy i hi) _
        · simpa using rpow_le_rpow_of_exponent_le (hw i hi) hγ1

/-! ### Hölder and reverse Hölder for power sums -/

/-- `(a * y ^ u) ^ (1 / p) * (a * y ^ v) ^ (1 / q) = a * y ^ (u / p + v / q)` when
`p⁻¹ + q⁻¹ = 1`. -/
private lemma rpow_mul_rpow_eq {p q u v α a y : ℝ} (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (ha : 0 ≤ a) (hy : 0 < y) :
    (a * y ^ u) ^ (1 / p) * (a * y ^ v) ^ (1 / q) = a * y ^ α := by
  have h1 : 1 / p + 1 / q = 1 := by simpa only [one_div] using hpq
  have h2 : u * (1 / p) + v * (1 / q) = α := by rw [← hα]; ring
  rw [mul_rpow ha (by positivity), mul_rpow ha (by positivity), mul_mul_mul_comm,
    ← rpow_add' ha (by rw [h1]; exact one_ne_zero), ← rpow_mul hy.le, ← rpow_mul hy.le,
    ← rpow_add hy, h1, h2, rpow_one]

private lemma sum_rpow_one_div_rpow {p : ℝ} (hp : p ≠ 0) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i ^ (1 / p)) ^ p = ∑ i ∈ s, f i :=
  sum_congr rfl fun i hi ↦ by rw [one_div, rpow_inv_rpow (hf i hi) hp]

/-- **Hölder's inequality for weighted power sums**: for conjugate exponents `p`, `q` and
`α = u / p + v / q`, `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`, `w i ≥ 0` and `x i > 0`. -/
theorem sum_mul_rpow_le_of_one_lt {p q u v α : ℝ} (hpq : p.HolderConjugate q)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
  have hf (γ : ℝ) : ∀ i ∈ s, 0 ≤ w i * x i ^ γ := fun i hi ↦
    mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  have H := inner_le_Lp_mul_Lq_of_nonneg s hpq (f := fun i ↦ (w i * x i ^ u) ^ (1 / p))
    (g := fun i ↦ (w i * x i ^ v) ^ (1 / q)) (fun i hi ↦ rpow_nonneg (hf u i hi) _)
    (fun i hi ↦ rpow_nonneg (hf v i hi) _)
  rwa [sum_congr rfl fun i hi ↦ rpow_mul_rpow_eq hpq.inv_add_inv_eq_one hα (hw i hi) (hx i hi),
    sum_rpow_one_div_rpow s hpq.ne_zero (hf u), sum_rpow_one_div_rpow s hpq.symm.ne_zero (hf v)]
    at H

/-- **Reverse Hölder inequality for weighted power sums**: for `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and
`α = u / p + v / q`, `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ`,
`w i ≥ 0` and `x i > 0`. -/
theorem le_sum_mul_rpow_of_lt_one {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  classical
  -- the indices with `w i = 0` contribute nothing, so we may assume `w i > 0`
  have hfilter (γ : ℝ) : ∑ i ∈ s with 0 < w i, w i * x i ^ γ = ∑ i ∈ s, w i * x i ^ γ :=
    sum_filter_of_ne fun i hi h ↦ (hw i hi).lt_of_ne (left_ne_zero_of_mul h).symm
  rw [← hfilter u, ← hfilter v, ← hfilter α]
  set t := s.filter (0 < w ·)
  have hwt : ∀ i ∈ t, 0 < w i := fun i hi ↦ (mem_filter.1 hi).2
  have hxt : ∀ i ∈ t, 0 < x i := fun i hi ↦ hx i (mem_filter.1 hi).1
  have hf (γ : ℝ) : ∀ i ∈ t, 0 < w i * x i ^ γ := fun i hi ↦
    mul_pos (hwt i hi) (rpow_pos_of_pos (hxt i hi) _)
  have H := Lp_mul_Lq_le_inner_of_lt_one t hp0 hp1 hpq
    (f := fun i ↦ (w i * x i ^ u) ^ (1 / p)) (g := fun i ↦ (w i * x i ^ v) ^ (1 / q))
    (fun i hi ↦ rpow_nonneg (hf u i hi).le _) (fun i hi ↦ rpow_pos_of_pos (hf v i hi) _)
  rwa [sum_congr rfl fun i hi ↦ rpow_mul_rpow_eq hpq hα (hwt i hi).le (hxt i hi),
    sum_rpow_one_div_rpow t hp0.ne' fun i hi ↦ (hf u i hi).le,
    sum_rpow_one_div_rpow t (neg_of_inv_add_inv_eq_one hp0 hp1 hpq).ne
      fun i hi ↦ (hf v i hi).le] at H

/-! ### Power means -/

/-- If the weights `w i ≥ 0` have total weight zero, every weighted sum vanishes. -/
private lemma sum_mul_eq_zero_of_sum_eq_zero (hw : ∀ i ∈ s, 0 ≤ w i) (hW : ∑ i ∈ s, w i = 0)
    (f : ι → ℝ) : ∑ i ∈ s, w i * f i = 0 :=
  sum_eq_zero fun i hi ↦ by rw [(sum_eq_zero_iff_of_nonneg hw).1 hW i hi, zero_mul]

/-- **Power mean inequality**, concave case: for `0 < α ≤ β`, `w i ≥ 0` and `x i ≥ 0`,
`S α ≤ W ^ (1 - α / β) * S β ^ (α / β)`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`W = ∑ i ∈ s, w i`. -/
theorem le_rpow_mean_of_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  have H := inner_le_weight_mul_Lp_of_nonneg s.attach ((one_le_div hα).2 hαβ)
    (fun i : s ↦ w i) (fun i : s ↦ x i ^ α) (fun i ↦ hw i i.2)
    (fun i ↦ rpow_nonneg (hx i i.2) _)
  simp only [sum_attach s (fun i ↦ w i * x i ^ α), sum_attach s w, inv_div] at H
  rwa [sum_attach s (fun i ↦ w i * (x i ^ α) ^ (β / α)), sum_congr rfl fun i hi ↦
    (by rw [rpow_rpow_div β (hx i hi) hα.ne'] : w i * (x i ^ α) ^ (β / α) = w i * x i ^ β)] at H

/-- **Power mean inequality**, convex case: for `0 < β ≤ α`, `w i ≥ 0` and `x i ≥ 0`,
`W ^ (1 - α / β) * S β ^ (α / β) ≤ S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`W = ∑ i ∈ s, w i`. -/
theorem rpow_mean_le_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  have hα : 0 < α := hβ.trans_le hβα
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ s, w i * x i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi) _)
  obtain hW | hW := (sum_nonneg hw).eq_or_lt
  · rw [sum_mul_eq_zero_of_sum_eq_zero s hw hW.symm, zero_rpow (by positivity), mul_zero]
    exact hS α
  calc (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β)
      ≤ (∑ i ∈ s, w i) ^ (1 - α / β) *
          ((∑ i ∈ s, w i) ^ (1 - β / α) * (∑ i ∈ s, w i * x i ^ α) ^ (β / α)) ^ (α / β) := by
        exact mul_le_mul_of_nonneg_left
          (rpow_le_rpow (hS β) (le_rpow_mean_of_le s hβ hβα hw hx) (by positivity))
          (rpow_nonneg hW.le _)
    _ = (∑ i ∈ s, w i) ^ (1 - α / β + (1 - β / α) * (α / β)) *
          (∑ i ∈ s, w i * x i ^ α) ^ (β / α * (α / β)) := by
        rw [mul_rpow (rpow_nonneg hW.le _) (rpow_nonneg (hS α) _), ← rpow_mul hW.le,
          ← rpow_mul (hS α), rpow_add hW, mul_assoc]
    _ = ∑ i ∈ s, w i * x i ^ α := by
        rw [show 1 - α / β + (1 - β / α) * (α / β) = 0 by field_simp; ring,
          show β / α * (α / β) = 1 by field_simp, rpow_zero, rpow_one, one_mul]

/-! ### Comparisons using `1 ≤ x i` -/

/-- If `w i ≥ 0`, `1 ≤ x i` and `0 < β ≤ α`, then `S β ≤ W ^ (1 - α / β) * S β ^ (α / β)`,
where `S β = ∑ i ∈ s, w i * x i ^ β` and `W = ∑ i ∈ s, w i`. -/
theorem sum_le_rpow_mean_of_one_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ β ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  obtain hW | hW := (sum_nonneg hw).eq_or_lt
  · rw [sum_mul_eq_zero_of_sum_eq_zero s hw hW.symm]
    positivity
  have hWS : ∑ i ∈ s, w i ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_le_sum fun i hi ↦ le_mul_of_one_le_right (hw i hi) (one_le_rpow (hx i hi) hβ.le)
  have hS : 0 < ∑ i ∈ s, w i * x i ^ β := hW.trans_le hWS
  have hc : 0 ≤ α / β - 1 := by rw [sub_nonneg]; exact (one_le_div hβ).2 hβα
  rw [show 1 - α / β = -(α / β - 1) by ring, rpow_neg hW.le, ← div_eq_inv_mul,
    le_div_iff₀ (rpow_pos_of_pos hW _)]
  calc (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i) ^ (α / β - 1)
      ≤ (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β - 1) := by gcongr
    _ = _ := by rw [rpow_sub_one hS.ne']; field_simp

/-- If `w i ≥ 0`, `1 ≤ x i` and `0 < α ≤ β`, then `W ^ (1 - α / β) * S β ^ (α / β) ≤ S β`,
where `S β = ∑ i ∈ s, w i * x i ^ β` and `W = ∑ i ∈ s, w i`. -/
theorem rpow_mean_le_sum_of_one_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ β := by
  have hβ : 0 < β := hα.trans_le hαβ
  obtain hW | hW := (sum_nonneg hw).eq_or_lt
  · rw [sum_mul_eq_zero_of_sum_eq_zero s hw hW.symm, zero_rpow (by positivity), mul_zero]
  have hWS : ∑ i ∈ s, w i ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_le_sum fun i hi ↦ le_mul_of_one_le_right (hw i hi) (one_le_rpow (hx i hi) hβ.le)
  have hS : 0 < ∑ i ∈ s, w i * x i ^ β := hW.trans_le hWS
  have hc : α / β - 1 ≤ 0 := by rw [sub_nonpos]; exact (div_le_one hβ).2 hαβ
  rw [show 1 - α / β = -(α / β - 1) by ring, rpow_neg hW.le, ← div_eq_inv_mul,
    div_le_iff₀ (rpow_pos_of_pos hW _)]
  calc (∑ i ∈ s, w i * x i ^ β) ^ (α / β)
      = (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β - 1) := by
        rw [rpow_sub_one hS.ne']; field_simp
    _ ≤ (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i) ^ (α / β - 1) := by
        exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hW hWS hc) hS.le

/-! ### Monotonicity of weighted `ℓ^γ` norms, using `1 ≤ w i` -/

/-- If `1 ≤ w i`, `0 ≤ x i` and `0 < β ≤ α`, then `S α ≤ S β ^ (α / β)`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem sum_rpow_le_rpow_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 1 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ α ≤ (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  calc ∑ i ∈ s, w i * x i ^ α = ∑ i ∈ s, w i * (x i ^ β) ^ (α / β) :=
        sum_congr rfl fun i hi ↦ by rw [rpow_rpow_div α (hx i hi) hβ.ne']
    _ ≤ _ := sum_mul_rpow_le_rpow_sum_mul s ((one_le_div hβ).2 hβα) hw fun i hi ↦
        rpow_nonneg (hx i hi) _

/-- If `1 ≤ w i`, `0 ≤ x i` and `0 < β ≤ α`, then `S α ^ (β / α) ≤ S β`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem sum_rpow_rpow_le_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 1 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i ^ α) ^ (β / α) ≤ ∑ i ∈ s, w i * x i ^ β := by
  have hα : 0 < α := hβ.trans_le hβα
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ s, w i * x i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (zero_le_one.trans (hw i hi)) (rpow_nonneg (hx i hi) _)
  calc (∑ i ∈ s, w i * x i ^ α) ^ (β / α)
      ≤ ((∑ i ∈ s, w i * x i ^ β) ^ (α / β)) ^ (β / α) := by
        exact rpow_le_rpow (hS α) (sum_rpow_le_rpow_of_le s hβ hβα hw hx) (by positivity)
    _ = ∑ i ∈ s, w i * x i ^ β := by
        rw [← rpow_mul (hS β), show α / β * (β / α) = 1 by field_simp, rpow_one]

/-- If `1 ≤ w i`, `0 ≤ x i`, `s` is nonempty and `0 ≤ α ≤ β` with `0 < β`, then
`S β ^ (α / β) ≤ S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem rpow_le_sum_rpow_of_le {α β : ℝ} (hs : s.Nonempty) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : 0 < β) (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤ ∑ i ∈ s, w i * x i ^ α := by
  calc _ ≤ ∑ i ∈ s, w i * (x i ^ β) ^ (α / β) :=
        rpow_sum_mul_le_sum_mul_rpow s (by positivity) ((div_le_one hβ).2 hαβ) hs hw
          fun i hi ↦ rpow_nonneg (hx i hi) _
    _ = _ := sum_congr rfl fun i hi ↦ by rw [rpow_rpow_div α (hx i hi) hβ.ne']

end Real
