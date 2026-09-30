/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Ozeki's inequality with the constant `n ^ 2 / 4` fails for arbitrary families

Ozeki's inequality is often quoted as follows: if `0 < m₁ ≤ a i ≤ M₁` and `0 < m₂ ≤ b i ≤ M₂` for
`i = 1, …, n`, then
`(∑ a i ^ 2) * (∑ b i ^ 2) - (∑ a i * b i) ^ 2 ≤ n ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2`.
Izumino and Seo, and Izumino, Mori and Seo, observed that this form is false, and showed that the
sharp constant for arbitrary families is `n ^ 2 / 3` instead of `n ^ 2 / 4`. This file records a
three-term example illustrating their observation: `a = (10, 10, 1)` and `b = (1, 10, 10)` give
`(∑ a i ^ 2) * (∑ b i ^ 2) - (∑ a i * b i) ^ 2 = 26001`, while
`3 ^ 2 / 4 * (10 * 10 - 1 * 1) ^ 2 = 22052.25`.

The bound with `n ^ 2 / 4` does hold when `a i` and `b i` are powers of one family, see
`Real.ozeki_rpow`, and when `a` and `b` monovary, see
`Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_monovaryOn`.

## References

* [N. Ozeki, *On the estimation of the inequalities by the maximum, or minimum values*]
  [ozeki_1968]
* [S. Izumino and Y. Seo, *On Ozeki's inequality and noncommutative covariance*]
  [izumino_seo_1997]
* [S. Izumino, H. Mori and Y. Seo, *On Ozeki's inequality*][izumino_mori_seo_1998]
-/

public section

namespace Counterexample

/-- **Ozeki**'s inequality with the constant `n ^ 2 / 4` fails for arbitrary families: there are
`a b : Fin 3 → ℝ` with `1 ≤ a i ≤ 10` and `1 ≤ b i ≤ 10` such that
`(∑ a i ^ 2) * (∑ b i ^ 2) - (∑ a i * b i) ^ 2 > 3 ^ 2 / 4 * (10 * 10 - 1 * 1) ^ 2`.
This illustrates the observation of Izumino–Seo and Izumino–Mori–Seo that the sharp constant for
arbitrary families is `n ^ 2 / 3`. -/
theorem not_forall_sum_sq_mul_sum_sq_sub_sq_le :
    ¬ ∀ (a b : Fin 3 → ℝ) (m₁ M₁ m₂ M₂ : ℝ), 0 < m₁ → 0 < m₂ →
      (∀ i, a i ∈ Set.Icc m₁ M₁) → (∀ i, b i ∈ Set.Icc m₂ M₂) →
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 ≤
        (3 : ℝ) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  intro h
  have := h ![10, 10, 1] ![1, 10, 10] 1 10 1 10 one_pos one_pos
    (fun i ↦ by fin_cases i <;> norm_num) (fun i ↦ by fin_cases i <;> norm_num)
  simp only [Fin.sum_univ_three] at this
  norm_num at this

end Counterexample
