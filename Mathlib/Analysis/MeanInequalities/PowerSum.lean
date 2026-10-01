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
compares these quantities for different exponents. Following
`Real.inner_le_weight_mul_Lp_of_nonneg`, we call `W ^ (1 - α / β) * S β ^ (α / β)` a
`weight_mul_Lp` term.

## Main results

* `Real.sum_mul_rpow_le_rpow_sum_mul`, `Real.rpow_sum_mul_le_sum_mul_rpow`:
  `∑ w i * y i ^ γ ≤ (∑ w i * y i) ^ γ` for `γ ≥ 1`, and the reverse inequality for `γ ≤ 1` when
  moreover `0 < ∑ w i * y i`, for `w i ≥ 0` and `y i ≥ 0` such that every `y i` is at most
  `∑ w i * y i` (for instance when `1 ≤ w i`).
* `Real.sum_rpow_le_rpow_sum`, `Real.rpow_sum_le_sum_rpow`: the unweighted case: for `y i ≥ 0`,
  `∑ y i ^ γ ≤ (∑ y i) ^ γ` for `γ ≥ 1`, and the reverse for `γ ≤ 1` when `0 < ∑ y i`.
* `Real.sum_mul_rpow_le_Lp_mul_Lq_of_one_lt`, `Real.Lp_mul_Lq_le_sum_mul_rpow_of_lt_one`:
  for `w i ≥ 0` and `0 < x i`, Hölder's inequality `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` for
  `α = u / p + v / q` and conjugate exponents `p`, `q` with `p > 1`, and its reverse for
  `0 < p < 1`.
* `Real.weight_mul_Lp_le_sum_mul_rpow`, `Real.sum_mul_rpow_le_weight_mul_Lp`: for `w i ≥ 0`, the
  power mean inequality `W ^ (1 - α / β) * S β ^ (α / β) ≤ S α` for `0 < β ≤ α`, and its reverse
  for `0 < α ≤ β`.
* `Real.le_rpow_one_sub_mul_rpow_of_le`, `Real.rpow_one_sub_mul_rpow_le_of_le`: for reals
  `0 < W ≤ S`, `S ≤ W ^ (1 - r) * S ^ r` if `1 ≤ r`, and `W ^ (1 - r) * S ^ r ≤ S` if `r ≤ 1`
  (where `0 ≤ W` suffices). With `r = α / β` they compare `S β` with the `weight_mul_Lp` term when
  `W ≤ S β`, for instance when `0 ≤ β`, `0 ≤ w i` and `1 ≤ x i`.
* `Real.sum_mul_rpow_le_rpow_sum_mul_rpow`, `Real.rpow_sum_mul_rpow_le_sum_mul_rpow`:
  monotonicity of the weighted `ℓ^γ` norms `S γ ^ (1 / γ)` for `w i ≥ 0`: `S α ≤ S β ^ (α / β)`
  for `0 < β ≤ α`, and `S β ^ (α / β) ≤ S α` for `α ≤ β` with `0 < β` and `0 < S β`, when every
  `x i ^ β` is at most `S β`.

Dujella, Jakšetić and Pečarić chain these inequalities in the unweighted case `w = 1` (their
Theorems 6 and 7).

## References

* [A. Dujella, J. Jakšetić and J. Pečarić, *Fibonacci numbers and Hölder inequality*]
  [dujella_jaksetic_pecaric]
-/

public section

open Finset

namespace Finset

variable {ι R : Type*} [NonUnitalNonAssocSemiring R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- If the weights `w i ≥ 0` have total weight zero, then every weighted sum
`∑ i ∈ s, w i * f i` vanishes. -/
theorem sum_mul_eq_zero_of_sum_eq_zero {s : Finset ι} {w : ι → R} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : ∑ i ∈ s, w i = 0) (f : ι → R) : ∑ i ∈ s, w i * f i = 0 :=
  sum_eq_zero fun i hi ↦ by rw [(sum_eq_zero_iff_of_nonneg hw).1 hW i hi, zero_mul]

end Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-- `(x ^ b) ^ (a / b) = x ^ a` for `0 ≤ x` and `b ≠ 0`. -/
@[simp]
lemma rpow_rpow_div {x : ℝ} (a : ℝ) {b : ℝ} (hx : 0 ≤ x) (hb : b ≠ 0) :
    (x ^ b) ^ (a / b) = x ^ a := by
  rw [← rpow_mul hx, mul_div_cancel₀ a hb]

/-! ### Superadditivity and subadditivity of `y ↦ y ^ γ` on finite sums -/

/-- For `γ ≥ 1`, `w i ≥ 0` and `y i ≥ 0` such that every `y i` is at most
`∑ j ∈ s, w j * y j`, `∑ i ∈ s, w i * y i ^ γ ≤ (∑ i ∈ s, w i * y i) ^ γ`. The hypothesis on
`y i` holds for instance if `1 ≤ w i`. -/
theorem sum_mul_rpow_le_rpow_sum_mul {γ : ℝ} (hγ : 1 ≤ γ) {y : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy : ∀ i ∈ s, y i ≤ ∑ j ∈ s, w j * y j) :
    ∑ i ∈ s, w i * y i ^ γ ≤ (∑ i ∈ s, w i * y i) ^ γ := by
  have hS : 0 ≤ ∑ i ∈ s, w i * y i := sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (hy0 i hi)
  have hγ' : 1 + (γ - 1) ≠ 0 := by linarith
  -- `y i ^ γ = y i * y i ^ (γ - 1) ≤ y i * S ^ (γ - 1)`, where `S = ∑ j ∈ s, w j * y j`
  calc ∑ i ∈ s, w i * y i ^ γ = ∑ i ∈ s, w i * y i * y i ^ (γ - 1) :=
        sum_congr rfl fun i hi ↦ by rw [mul_assoc, ← rpow_one_add' (hy0 i hi) hγ', add_sub_cancel]
    _ ≤ ∑ i ∈ s, w i * y i * (∑ j ∈ s, w j * y j) ^ (γ - 1) := sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left (rpow_le_rpow (hy0 i hi) (hy i hi) (by linarith))
          (mul_nonneg (hw i hi) (hy0 i hi))
    _ = _ := by rw [← sum_mul, ← rpow_one_add' hS hγ', add_sub_cancel]

/-- For `γ ≤ 1`, `w i ≥ 0` and `y i ≥ 0` such that every `y i` is at most
`∑ j ∈ s, w j * y j` and this sum is positive,
`(∑ i ∈ s, w i * y i) ^ γ ≤ ∑ i ∈ s, w i * y i ^ γ`. The hypothesis on `y i` holds for instance
if `1 ≤ w i`. -/
theorem rpow_sum_mul_le_sum_mul_rpow {γ : ℝ} (hγ : γ ≤ 1) {y : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy : ∀ i ∈ s, y i ≤ ∑ j ∈ s, w j * y j)
    (hS : 0 < ∑ i ∈ s, w i * y i) :
    (∑ i ∈ s, w i * y i) ^ γ ≤ ∑ i ∈ s, w i * y i ^ γ := by
  -- `S ^ (γ - 1) * y i ≤ y i ^ (γ - 1) * y i = y i ^ γ`, where `S = ∑ j ∈ s, w j * y j`
  calc (∑ i ∈ s, w i * y i) ^ γ = ∑ i ∈ s, w i * y i * (∑ j ∈ s, w j * y j) ^ (γ - 1) := by
        rw [← sum_mul, rpow_sub_one hS.ne', mul_div_cancel₀ _ hS.ne']
    _ ≤ ∑ i ∈ s, w i * y i ^ γ := sum_le_sum fun i hi ↦ by
        obtain hyi | hyi := (hy0 i hi).eq_or_lt
        · rw [← hyi, mul_zero, zero_mul]
          exact mul_nonneg (hw i hi) (rpow_nonneg le_rfl _)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
        calc y i * (∑ j ∈ s, w j * y j) ^ (γ - 1) ≤ y i * y i ^ (γ - 1) :=
              mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hyi (hy i hi) (by linarith))
                hyi.le
          _ = y i ^ γ := by rw [rpow_sub_one hyi.ne', mul_div_cancel₀ _ hyi.ne']

/-- For `γ ≥ 1` and `y i ≥ 0`, `∑ i ∈ s, y i ^ γ ≤ (∑ i ∈ s, y i) ^ γ`. -/
theorem sum_rpow_le_rpow_sum {γ : ℝ} (hγ : 1 ≤ γ) {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, y i ^ γ ≤ (∑ i ∈ s, y i) ^ γ := by
  simpa using sum_mul_rpow_le_rpow_sum_mul s hγ (w := fun _ ↦ 1) (fun _ _ ↦ zero_le_one) hy
    fun i hi ↦ by simpa using single_le_sum hy hi

/-- For `γ ≤ 1`, `y i ≥ 0` and `0 < ∑ i ∈ s, y i`, `(∑ i ∈ s, y i) ^ γ ≤ ∑ i ∈ s, y i ^ γ`. -/
theorem rpow_sum_le_sum_rpow {γ : ℝ} (hγ : γ ≤ 1) {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i)
    (hS : 0 < ∑ i ∈ s, y i) : (∑ i ∈ s, y i) ^ γ ≤ ∑ i ∈ s, y i ^ γ := by
  simpa using rpow_sum_mul_le_sum_mul_rpow s hγ (w := fun _ ↦ 1) (fun _ _ ↦ zero_le_one) hy
    (fun i hi ↦ by simpa using single_le_sum hy hi) (by simpa using hS)

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
theorem sum_mul_rpow_le_Lp_mul_Lq_of_one_lt {p q u v α : ℝ} (hpq : p.HolderConjugate q)
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
theorem Lp_mul_Lq_le_sum_mul_rpow_of_lt_one {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
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
    sum_rpow_one_div_rpow t (neg_of_lt_one_of_inv_add_inv_eq_one hp0 hp1 hpq).ne
      fun i hi ↦ (hf v i hi).le] at H

/-! ### Power means -/

/-- **Power mean inequality**, concave case: for `0 < α ≤ β`, `w i ≥ 0` and `x i ≥ 0`,
`S α ≤ W ^ (1 - α / β) * S β ^ (α / β)`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`W = ∑ i ∈ s, w i`. -/
theorem sum_mul_rpow_le_weight_mul_Lp {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  -- `Real.inner_le_weight_mul_Lp_of_nonneg` asks for nonnegativity everywhere, not only on `s`,
  -- so we apply it on `s.attach`, where the hypotheses `hw` and `hx` are available.
  have H := inner_le_weight_mul_Lp_of_nonneg s.attach ((one_le_div hα).2 hαβ)
    (fun i : s ↦ w i) (fun i : s ↦ x i ^ α) (fun i ↦ hw i i.2)
    (fun i ↦ rpow_nonneg (hx i i.2) _)
  simp only [sum_attach s (fun i ↦ w i * x i ^ α), sum_attach s w, inv_div] at H
  rwa [sum_attach s (fun i ↦ w i * (x i ^ α) ^ (β / α)), sum_congr rfl fun i hi ↦
    (by rw [rpow_rpow_div β (hx i hi) hα.ne'] : w i * (x i ^ α) ^ (β / α) = w i * x i ^ β)] at H

/-- **Power mean inequality**, convex case: for `0 < β ≤ α`, `w i ≥ 0` and `x i ≥ 0`,
`W ^ (1 - α / β) * S β ^ (α / β) ≤ S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`W = ∑ i ∈ s, w i`. -/
theorem weight_mul_Lp_le_sum_mul_rpow {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  have hα : 0 < α := hβ.trans_le hβα
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ s, w i * x i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi) _)
  obtain hW | hW := (sum_nonneg hw).eq_or_lt
  · rw [sum_mul_eq_zero_of_sum_eq_zero hw hW.symm, zero_rpow (by positivity), mul_zero]
    exact hS α
  calc (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β)
      ≤ (∑ i ∈ s, w i) ^ (1 - α / β) *
          ((∑ i ∈ s, w i) ^ (1 - β / α) * (∑ i ∈ s, w i * x i ^ α) ^ (β / α)) ^ (α / β) := by
        exact mul_le_mul_of_nonneg_left
          (rpow_le_rpow (hS β) (sum_mul_rpow_le_weight_mul_Lp s hβ hβα hw hx) (by positivity))
          (rpow_nonneg hW.le _)
    _ = (∑ i ∈ s, w i) ^ (1 - α / β + (1 - β / α) * (α / β)) *
          (∑ i ∈ s, w i * x i ^ α) ^ (β / α * (α / β)) := by
        rw [mul_rpow (rpow_nonneg hW.le _) (rpow_nonneg (hS α) _), ← rpow_mul hW.le,
          ← rpow_mul (hS α), rpow_add hW, mul_assoc]
    _ = ∑ i ∈ s, w i * x i ^ α := by
        rw [show 1 - α / β + (1 - β / α) * (α / β) = 0 by field_simp; ring,
          show β / α * (α / β) = 1 by field_simp, rpow_zero, rpow_one, one_mul]

/-! ### Comparisons using `W ≤ S` -/

/-- If `0 < W ≤ S` and `1 ≤ r`, then `S ≤ W ^ (1 - r) * S ^ r`. For `W = ∑ i ∈ s, w i`,
`S = ∑ i ∈ s, w i * x i ^ β` and `r = α / β` this compares `S` with the `weight_mul_Lp` term; the
hypothesis `W ≤ S` then holds for instance if `0 ≤ β`, `0 ≤ w i` and `1 ≤ x i`. -/
theorem le_rpow_one_sub_mul_rpow_of_le {W S r : ℝ} (hW : 0 < W) (hWS : W ≤ S) (hr : 1 ≤ r) :
    S ≤ W ^ (1 - r) * S ^ r := by
  have hS : 0 < S := hW.trans_le hWS
  calc S = S ^ (1 - r) * S ^ r := by rw [← rpow_add hS, sub_add_cancel, rpow_one]
    _ ≤ W ^ (1 - r) * S ^ r := by
      gcongr ?_ * _
      exact rpow_le_rpow_of_nonpos hW hWS (by linarith)

/-- If `0 ≤ W ≤ S` and `r ≤ 1`, then `W ^ (1 - r) * S ^ r ≤ S`. For `W = ∑ i ∈ s, w i`,
`S = ∑ i ∈ s, w i * x i ^ β` and `r = α / β` this compares the `weight_mul_Lp` term with `S`; the
hypothesis `W ≤ S` then holds for instance if `0 ≤ β`, `0 ≤ w i` and `1 ≤ x i`. -/
theorem rpow_one_sub_mul_rpow_le_of_le {W S r : ℝ} (hW : 0 ≤ W) (hWS : W ≤ S) (hr : r ≤ 1) :
    W ^ (1 - r) * S ^ r ≤ S := by
  obtain rfl | hr := hr.eq_or_lt
  · simp
  obtain rfl | hW := hW.eq_or_lt
  · rwa [zero_rpow (by linarith), zero_mul]
  have hS : 0 < S := hW.trans_le hWS
  calc W ^ (1 - r) * S ^ r ≤ S ^ (1 - r) * S ^ r := by gcongr
    _ = S := by rw [← rpow_add hS, sub_add_cancel, rpow_one]

/-! ### Monotonicity of weighted `ℓ^γ` norms -/

/-- If `w i ≥ 0`, `x i ≥ 0`, `0 < β ≤ α` and every `x i ^ β` is at most `S β`, then
`S α ≤ S β ^ (α / β)`, where `S γ = ∑ i ∈ s, w i * x i ^ γ`. The hypothesis on `x i ^ β` holds for
instance if `1 ≤ w i`. -/
theorem sum_mul_rpow_le_rpow_sum_mul_rpow {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx : ∀ i ∈ s, x i ^ β ≤ ∑ j ∈ s, w j * x j ^ β) :
    ∑ i ∈ s, w i * x i ^ α ≤ (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  calc ∑ i ∈ s, w i * x i ^ α = ∑ i ∈ s, w i * (x i ^ β) ^ (α / β) :=
        sum_congr rfl fun i hi ↦ by rw [rpow_rpow_div α (hx0 i hi) hβ.ne']
    _ ≤ _ := sum_mul_rpow_le_rpow_sum_mul s ((one_le_div hβ).2 hβα) hw
        (fun i hi ↦ rpow_nonneg (hx0 i hi) _) hx

/-- If `w i ≥ 0`, `x i ≥ 0`, `α ≤ β` with `0 < β`, every `x i ^ β` is at most `S β` and
`0 < S β`, then `S β ^ (α / β) ≤ S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ`. The hypothesis on
`x i ^ β` holds for instance if `1 ≤ w i`. -/
theorem rpow_sum_mul_rpow_le_sum_mul_rpow {α β : ℝ} (hαβ : α ≤ β) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx : ∀ i ∈ s, x i ^ β ≤ ∑ j ∈ s, w j * x j ^ β) (hS : 0 < ∑ i ∈ s, w i * x i ^ β) :
    (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤ ∑ i ∈ s, w i * x i ^ α := by
  calc _ ≤ ∑ i ∈ s, w i * (x i ^ β) ^ (α / β) :=
        rpow_sum_mul_le_sum_mul_rpow s ((div_le_one hβ).2 hαβ) hw
          (fun i hi ↦ rpow_nonneg (hx0 i hi) _) hx hS
    _ = _ := sum_congr rfl fun i hi ↦ by rw [rpow_rpow_div α (hx0 i hi) hβ.ne']

end Real
