/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Jensen

/-!
# Chains of weighted power-sum inequalities

For weights `w i` and positive reals `x i`, `i ∈ s`, write `S γ = ∑ i ∈ s, w i * x i ^ γ` for the
weighted power sum and `W = ∑ i ∈ s, w i` for the total weight.  Dujella, Jakšetić and Pečarić
chained Hölder's inequality, Jensen's inequality and the monotonicity of power means into
inequalities of the form
`S u ^ (1 / p) * S v ^ (1 / q) ≥ S α ≥ W ^ (1 - α / β) * S β ^ (α / β) ≥ S β ≥ S α ^ (β / α)`,
where `α = u / p + v / q`, in the unweighted case `w = 1`.  This file proves the weighted chains.
Hölder's inequality and Jensen's inequality hold for arbitrary nonnegative weights; the steps
that compare `S α ^ (β / α)` with `S β` (monotonicity of `ℓ^γ` norms) need `1 ≤ w i`, and the
steps that compare `S β` with `W` need `1 ≤ x i`.

## Main results

* `Real.Lp_mul_Lq_le_inner_of_lt_one`: the reverse Hölder inequality for `0 < p < 1`.
* `Real.sum_mul_rpow_le_of_one_lt`, `Real.le_sum_mul_rpow_of_lt_one`: weighted Hölder and
  reverse Hölder for power sums.
* `Real.powerSum_chain_of_one_lt_of_le`, `Real.powerSum_chain_of_one_lt_of_lt`,
  `Real.powerSum_chain_of_lt_one_of_le`, `Real.powerSum_chain_of_lt_one_of_lt`: the four weighted
  chains (Theorems 6 and 7 of Dujella–Jakšetić–Pečarić in the case `w = 1`).

Throughout, `q` is the conjugate exponent: `p⁻¹ + q⁻¹ = 1`, so `q > 1` when `p > 1` and `q < 0`
when `0 < p < 1`.
-/

@[expose] public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-! ### Hölder and reverse Hölder -/

/-- **Reverse Hölder inequality**: for `0 < p < 1` and `p⁻¹ + q⁻¹ = 1` (so `q < 0`), and positive
`f`, `g`, `(∑ f ^ p) ^ (1 / p) * (∑ g ^ q) ^ (1 / q) ≤ ∑ f * g`. -/
theorem Lp_mul_Lq_le_inner_of_lt_one {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) ≤ ∑ i ∈ s, f i * g i := by
  sorry

/-- **Weighted Hölder inequality for power sums**: for `p > 1`, `p⁻¹ + q⁻¹ = 1` and
`α = u / p + v / q`, `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`. -/
theorem sum_mul_rpow_le_of_one_lt {p q u v α : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
  sorry

/-- **Weighted reverse Hölder inequality for power sums**: for `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and
`α = u / p + v / q`, `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`. -/
theorem le_sum_mul_rpow_of_lt_one {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 < w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  sorry

/-! ### Power means (Jensen) -/

/-- Jensen's inequality for the convex power `y ↦ y ^ (α / β)`, `0 < β ≤ α`:
`W ^ (1 - α / β) * S β ^ (α / β) ≤ S α`. -/
theorem rpow_mean_le_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  sorry

/-- Jensen's inequality for the concave power `y ↦ y ^ (α / β)`, `0 < α ≤ β`:
`S α ≤ W ^ (1 - α / β) * S β ^ (α / β)`. -/
theorem le_rpow_mean_of_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  sorry

/-! ### Comparisons using `1 ≤ x i` -/

/-- If `1 ≤ x i` and `0 < β ≤ α`, then `S β ≤ W ^ (1 - α / β) * S β ^ (α / β)`. -/
theorem sum_le_mean_rpow_of_one_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ β ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  sorry

/-- If `1 ≤ x i` and `0 < α ≤ β`, then `W ^ (1 - α / β) * S β ^ (α / β) ≤ S β`. -/
theorem mean_rpow_le_sum_of_one_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ β := by
  sorry

/-! ### Monotonicity of weighted `ℓ^γ` norms, using `1 ≤ w i` -/

/-- If `1 ≤ w i` and `0 < β ≤ α`, then `S α ^ (β / α) ≤ S β`. -/
theorem sum_rpow_rpow_le_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 1 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ α) ^ (β / α) ≤ ∑ i ∈ s, w i * x i ^ β := by
  sorry

/-- If `1 ≤ w i` and `0 < β ≤ α`, then `S α ≤ S β ^ (α / β)`. -/
theorem sum_rpow_le_rpow_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 1 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤ (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  sorry

/-- If `1 ≤ w i`, `s` is nonempty and `0 ≤ α ≤ β` with `0 < β`, then `S β ^ (α / β) ≤ S α`. -/
theorem rpow_le_sum_rpow_of_le {α β : ℝ} (hs : s.Nonempty) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : 0 < β) (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤ ∑ i ∈ s, w i * x i ^ α := by
  sorry

/-! ### The four chains -/

/-- **Weighted power-sum chain, `p > 1`, `α ≥ β`** (Dujella–Jakšetić–Pečarić, Theorem 6(i),
for `w = 1`). -/
theorem powerSum_chain_of_one_lt_of_le {p q u v α β : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hβ : 0 < β) (hβα : β ≤ α) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
        (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ∧
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
        ∑ i ∈ s, w i * x i ^ α ∧
      ∑ i ∈ s, w i * x i ^ β ≤
        (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ∧
      (∑ i ∈ s, w i * x i ^ α) ^ (β / α) ≤ ∑ i ∈ s, w i * x i ^ β := by
  sorry

/-- **Weighted power-sum chain, `p > 1`, `0 ≤ α < β`** (Dujella–Jakšetić–Pečarić,
Theorem 6(ii), for `w = 1`). -/
theorem powerSum_chain_of_one_lt_of_lt {p q u v α β : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hαβ : α < β) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
        (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ∧
      (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤ ∑ i ∈ s, w i * x i ^ α := by
  sorry

/-- **Weighted power-sum chain, `0 < p < 1`, `α ≥ β`** (Dujella–Jakšetić–Pečarić,
Theorem 7(i), for `w = 1`). -/
theorem powerSum_chain_of_lt_one_of_le {p q u v α β : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
        ∑ i ∈ s, w i * x i ^ α ∧
      ∑ i ∈ s, w i * x i ^ α ≤ (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  sorry

/-- **Weighted power-sum chain, `0 < p < 1`, `0 < α < β`** (Dujella–Jakšetić–Pečarić,
Theorem 7(ii), for `w = 1`). -/
theorem powerSum_chain_of_lt_one_of_lt {p q u v α β : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α) (hαβ : α < β)
    (hs : s.Nonempty) (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
        ∑ i ∈ s, w i * x i ^ α ∧
      ∑ i ∈ s, w i * x i ^ α ≤
        (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ∧
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
        ∑ i ∈ s, w i * x i ^ β ∧
      ∑ i ∈ s, w i * x i ^ β ≤ (∑ i ∈ s, w i * x i ^ α) ^ (β / α) := by
  sorry

end Real
