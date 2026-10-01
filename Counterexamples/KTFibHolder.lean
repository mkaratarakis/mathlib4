/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Dickson

/-!
# Weighted Hölder chains for `(k, t)`-Lucas numbers need `1 ≤ k` or `1 ≤ t`

For weights `w i ≥ 0` and positive `x i`, write `S γ = ∑ i, w i * x i ^ γ`. The comparison
`S α ≤ S β ^ (α / β)` for `0 < β ≤ α` (`Real.sum_mul_rpow_le_rpow_sum_mul_rpow`) needs every
`x i ^ β` to be at most `S β`; for the `(k, t)`-Lucas numbers `L` with the weights `t ^ (n - i)` and
`β = 2` this holds when `1 ≤ k` or `1 ≤ t`. This file shows that the hypothesis cannot be dropped:

* `Counterexample.rpow_div_le_iff_one_le`: for a single term, `S α ^ (β / α) ≤ S β` holds if and
  only if the weight is at least `1`.
* `Counterexample.not_forall_sum_pow_mul_lucas_rpow_le`: for `k = 1 / 2`, `t = 1 / 32` and `n = 2`
  the conclusion `S 4 ≤ S 2 ^ 2` of `KTFib.holder_lucas_of_lt_one_of_two_le` fails; the numbers
  are in `Counterexample.lucas_one_div_two_one_div_thirty_two`.

## References

* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
-/

public section

open Finset

namespace Counterexample

/-- The `(k, t)`-Lucas numbers for `k = 1 / 2` and `t = 1 / 32`, at `n = 2`: `L 1 = 1 / 2`,
`L 2 = 5 / 16`, and with the weights `t ^ (2 - i)` the sum of squares is
`S 2 = ∑ i ∈ Icc 1 2, t ^ (2 - i) * L i ^ 2 = (L 2 * L 3 - 2 * k * t ^ 2) / k = 27 / 256`, which is
smaller than `L 1 ^ 2 = 1 / 4`; moreover `S 4 = ∑ i ∈ Icc 1 2, t ^ (2 - i) * L i ^ 4 = 753 / 65536`
while `S 2 ^ (4 / 2) = 729 / 65536`. -/
theorem lucas_one_div_two_one_div_thirty_two {L : ℕ → ℝ} (hL0 : L 0 = 2) (hL1 : L 1 = 1 / 2)
    (hL : ∀ n, L (n + 2) = 1 / 2 * L (n + 1) + 1 / 32 * L n) :
    L 2 = 5 / 16 ∧
      ∑ i ∈ Icc 1 2, (1 / 32 : ℝ) ^ (2 - i) * L i ^ 2 = 27 / 256 ∧
      (L 2 * L 3 - 2 * (1 / 2) * (1 / 32) ^ 2) / (1 / 2) = 27 / 256 ∧
      (27 / 256 : ℝ) < L 1 ^ 2 ∧
      ∑ i ∈ Icc 1 2, (1 / 32 : ℝ) ^ (2 - i) * L i ^ (4 : ℝ) = 753 / 65536 ∧
      (27 / 256 : ℝ) ^ ((4 : ℝ) / 2) = 729 / 65536 := by
  have hL2 : L 2 = 5 / 16 := by rw [hL, hL1, hL0]; norm_num
  have hL3 : L 3 = 11 / 64 := by rw [hL, hL2, hL1]; norm_num
  have e4 (y : ℝ) : y ^ (4 : ℝ) = y ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  have e2 : (4 : ℝ) / 2 = (2 : ℕ) := by norm_num
  rw [show Icc 1 2 = {1, 2} by rfl, sum_pair (by norm_num), sum_pair (by norm_num), e4, e4, e2,
    Real.rpow_natCast, hL1, hL2, hL3]
  norm_num

/-- The hypothesis `1 ≤ k ∨ 1 ≤ t` of `KTFib.holder_lucas_of_lt_one_of_two_le` cannot be dropped:
for `0 < k < 1` and small `t > 0` the bound
`∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤ ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2)` can fail,
for instance for `k = 1 / 2`, `t = 1 / 32`, `n = 2`, `p = 1 / 2`, `q = -1`, `u = 2`, `v = 0` and
`α = 4` (see `Counterexample.lucas_one_div_two_one_div_thirty_two`). -/
theorem not_forall_sum_pow_mul_lucas_rpow_le :
    ¬ ∀ (k t : ℝ) (L : ℕ → ℝ) (n : ℕ) (p q u v α : ℝ), 0 < k → 0 < t → L 0 = 2 → L 1 = k →
      (∀ n, L (n + 2) = k * L (n + 1) + t * L n) → 0 < p → p < 1 → p⁻¹ + q⁻¹ = 1 →
      u / p + v / q = α → 2 ≤ α →
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) := by
  intro h
  -- the `(1 / 2, 1 / 32)`-Lucas sequence, as values of Dickson polynomials
  set L : ℕ → ℝ := fun n ↦ (Polynomial.dickson 1 (-(1 / 32)) n).eval (1 / 2) with hLdef
  have hL : ∀ n, L (n + 2) = 1 / 2 * L (n + 1) + 1 / 32 * L n := fun n ↦ by
    simp only [hLdef, Polynomial.dickson_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hL0 : L 0 = 2 := by simp [hLdef]; norm_num
  have hL1 : L 1 = 1 / 2 := by simp [hLdef]
  have h' := h (1 / 2) (1 / 32) L 2 (1 / 2) (-1) 2 0 4 (by norm_num) (by norm_num) hL0 hL1 hL
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, -, hD, -, hS4, hD2⟩ := lucas_one_div_two_one_div_thirty_two hL0 hL1 hL
  rw [hS4, hD, hD2] at h'
  norm_num at h'

/-- For a single term, the comparison `S α ^ (β / α) ≤ S β` of weighted power sums
`S γ = w * x ^ γ` (as in `Real.sum_mul_rpow_le_rpow_sum_mul_rpow`) holds exactly when the weight is
at least `1`: for `0 < w`, `0 < x` and `0 < β < α`, `(w * x ^ α) ^ (β / α) ≤ w * x ^ β ↔ 1 ≤ w`. The
hypothesis `x ^ β ≤ S β` of `Real.sum_mul_rpow_le_rpow_sum_mul_rpow` is `1 ≤ w` as well. -/
theorem rpow_div_le_iff_one_le {w x α β : ℝ} (hw : 0 < w) (hx : 0 < x) (hβ : 0 < β)
    (hβα : β < α) :
    (w * x ^ α) ^ (β / α) ≤ w * x ^ β ↔ 1 ≤ w := by
  have hα : 0 < α := hβ.trans hβα
  rw [Real.mul_rpow hw.le (by positivity), ← Real.rpow_mul hx.le, mul_div_cancel₀ _ hα.ne',
    mul_le_mul_iff_left₀ (by positivity)]
  constructor
  · intro h
    by_contra h1
    have := Real.rpow_lt_rpow_of_exponent_gt hw (not_le.1 h1) ((div_lt_one hα).2 hβα)
    rw [Real.rpow_one] at this
    linarith
  · intro h1
    calc w ^ (β / α) ≤ w ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 ((div_le_one hα).2 hβα.le)
      _ = w := Real.rpow_one w

end Counterexample
