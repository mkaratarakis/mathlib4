/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.ConverseHolder
public import Mathlib.NumberTheory.KTFibonacci.Identities

/-!
# Hölder-type inequalities for `(k, t)`-Fibonacci and `(k, t)`-Lucas numbers

Let `k, t` be real, and let `F`, `L` be the `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences:
`F 0 = 0`, `F 1 = 1`, `L 0 = 2`, `L 1 = k`, both satisfying `X (n + 2) = k * X (n + 1) + t * X n`.
This file proves the `(k, t)` versions of the results of

> H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder inequality*,
> arXiv:2609.33573,

which treats `t = 1`.  The power sums are weighted by `t ^ (n - i)`: this is exactly the weight
for which the sums of squares and of consecutive products telescope, and it disappears at
`t = 1`.  With `W = ∑ i ∈ [1, n], t ^ (n - i)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`,
`P = (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k`:

* `KTFib.sum_sq_lucas`, `KTFib.sum_sq_fib`, `KTFib.sum_lucas_mul_succ` (Theorem 1.1 of
  Batte–Kaggwa at `t = 1`): `∑ t ^ (n - i) * L i ^ 2 = D`,
  `∑ t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k`, `∑ t ^ (n - i) * L i * L (i + 1) = P`.
* `KTFib.holder_sandwich_*` (Theorem 1.2): the four Hölder sandwiches for
  `∑ t ^ (n - i) * L i ^ α`, for `k ≥ 1` and `t ≥ 1`.
* `KTFib.converse_holder_lucas_*` (Theorem 1.3): the converse Hölder refinements, `t > 0`.
* `KTFib.cauchy_conversion_lucas` (Theorem 1.4): the converse Cauchy refinements for
  `x i = L i * L (i + 1)`, `t > 0`.
* `KTFib.sq_sum_fib_two_mul_le`, `KTFib.sq_sum_fib_two_mul_eq_iff` (Theorem 1.5): the
  cross-family bound `(∑ t ^ (n - i) * F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * D`, with equality
  exactly for `n = 1`; and its closed form `KTFib.sq_fib_sub_le`.
* `KTFib.sum_fib`, `KTFib.sum_lucas`, `KTFib.sum_fib_odd`, ... (Theorem 4.1).
-/

@[expose] public section

open Finset

namespace KTFib

variable {k t : ℝ} {F L : ℕ → ℝ}

/-! ### Closed forms (Theorem 1.1, Theorem 4.1) -/

section ClosedForms

/-- `∑ i ∈ [1, n], t ^ (n - i) * L i ^ 2 = (L n * L (n + 1) - 2 * k * t ^ n) / k`. -/
theorem sum_sq_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = (L n * L (n + 1) - 2 * k * t ^ n) / k := by
  sorry

/-- `∑ i ∈ [1, n], t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k`. -/
theorem sum_sq_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k := by
  sorry

/-- `∑ i ∈ [1, n], t ^ (n - i) * (L i * L (i + 1))` in closed form. -/
theorem sum_lucas_mul_succ (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
      (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k := by
  sorry

/-- `∑ i ∈ [1, n], F i = (F (n + 1) + t * F n - 1) / (k + t - 1)`. -/
theorem sum_fib (hkt : k + t ≠ 1) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i = (F (n + 1) + t * F n - 1) / (k + t - 1) := by
  sorry

/-- `∑ i ∈ [1, n], L i = (L (n + 1) + t * L n - k - 2 * t) / (k + t - 1)`. -/
theorem sum_lucas (hkt : k + t ≠ 1) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i = (L (n + 1) + t * L n - k - 2 * t) / (k + t - 1) := by
  sorry

/-- `∑ i ∈ [1, n], t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k`. -/
theorem sum_fib_odd (hk : k ≠ 0) (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k := by
  sorry

/-- `∑ i ∈ [1, n], t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k`. -/
theorem sum_fib_even (hk : k ≠ 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k := by
  sorry

/-- `∑ i ∈ [1, n], t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k`. -/
theorem sum_lucas_odd (hk : k ≠ 0) (hL0 : L 0 = 2) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k := by
  sorry

/-- `∑ i ∈ [1, n], t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k`. -/
theorem sum_lucas_even (hk : k ≠ 0) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k := by
  sorry

end ClosedForms

/-! ### Hölder sandwiches (Theorem 1.2) -/

section Sandwich

variable (hk : 1 ≤ k) (ht : 1 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht hL0 hL1 hL

/-- **Hölder sandwich, `p > 1`, `α ≥ 2`.** -/
theorem holder_sandwich_of_one_lt_of_two_le {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) * D ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      D ≤ (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) * D ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α) ^ (2 / α) ≤ D := by
  sorry

/-- **Hölder sandwich, `p > 1`, `0 ≤ α < 2`.** -/
theorem holder_sandwich_of_one_lt_of_lt_two {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ∧
      D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α := by
  sorry

/-- **Hölder sandwich, `0 < p < 1`, `α ≥ 2`.** -/
theorem holder_sandwich_of_lt_one_of_two_le {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤ D ^ (α / 2) := by
  sorry

/-- **Hölder sandwich, `0 < p < 1`, `0 < α < 2`.** -/
theorem holder_sandwich_of_lt_one_of_lt_two {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α)
    (hα2 : α < 2) (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) * D ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) * D ^ (α / 2) ≤ D ∧
      D ≤ (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α) ^ (2 / α) := by
  sorry

end Sandwich

/-! ### Converse Hölder refinements (Theorem 1.3) -/

section ConverseHolder

variable (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht hL0 hL1 hL

/-- **Converse Hölder refinement, `p > 1`.**  For `n ≥ 2`, `u ≠ v` and `u / p + v / q = 2`,
with `m, M` the smaller and larger of `L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)`. -/
theorem converse_holder_lucas_of_one_lt {n : ℕ} (hn : 2 ≤ n) {p q u v m M D : ℝ}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    0 < m ∧ m < M ∧
      (M - m) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u +
          (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v ≤
        (M ^ p - m ^ p) * D ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          D := by
  sorry

/-- **Converse Hölder refinement, `0 < p < 1`**: both inequalities of
`KTFib.converse_holder_lucas_of_one_lt` reverse. -/
theorem converse_holder_lucas_of_lt_one {n : ℕ} (hn : 2 ≤ n) {p q u v m M D : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    0 < m ∧ m < M ∧
      (M ^ p - m ^ p) * D ≤
        (M - m) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u +
          (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v ∧
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          D ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) := by
  sorry

end ConverseHolder

/-! ### Converse Cauchy refinements (Theorem 1.4) -/

section CauchyConversion

variable (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht hL0 hL1 hL

/-- **Converse Cauchy refinements for `x i = L i * L (i + 1)`.**  For `u + v = 2`, with
`m₁, M₁` (resp. `m₂, M₂`) the smaller and larger of `x 1 ^ (u / 2)`, `x n ^ (u / 2)` (resp.
`x 1 ^ (v / 2)`, `x n ^ (v / 2)`), and `P` the closed form of `∑ t ^ (n - i) * x i`. -/
theorem cauchy_conversion_lucas {n : ℕ} (hn : 1 ≤ n) {u v m₁ M₁ m₂ M₂ P : ℝ} (huv : u + v = 2)
    (hm₁ : m₁ = min ((L 1 * L 2) ^ (u / 2)) ((L n * L (n + 1)) ^ (u / 2)))
    (hM₁ : M₁ = max ((L 1 * L 2) ^ (u / 2)) ((L n * L (n + 1)) ^ (u / 2)))
    (hm₂ : m₂ = min ((L 1 * L 2) ^ (v / 2)) ((L n * L (n + 1)) ^ (v / 2)))
    (hM₂ : M₂ = max ((L 1 * L 2) ^ (v / 2)) ((L n * L (n + 1)) ^ (v / 2)))
    (hP : P = (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k) :
    (1 ≤ (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ u) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ v) / P ^ 2 ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ u) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ v) / P ^ 2 ≤
        (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4) ∧
    (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ u) / P -
        P / (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ v) ≤
      (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2 ∧
    (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ u) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ v) - P ^ 2 ≤
      (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 ∧
    ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ v +
        m₂ * M₂ / (M₁ * m₁) * ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ u ≤
      (M₂ / m₁ + m₂ / M₁) * P := by
  sorry

end CauchyConversion

/-! ### The cross-family bound (Theorem 1.5) -/

section CrossFamily

variable (hk : 0 < k) (ht : 0 < t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
  (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht hF0 hF1 hF hL0 hL1 hL

/-- **Cross-family Cauchy–Schwarz bound.** -/
theorem sq_sum_fib_two_mul_le (n : ℕ) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
      F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) := by
  sorry

/-- **Equality case of the cross-family bound**: for `n ≥ 1`, equality holds exactly when
`n = 1`. -/
theorem sq_sum_fib_two_mul_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
        F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ↔ n = 1 := by
  sorry

/-- **The cross-family bound in closed form**:
`(F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)`. -/
theorem sq_fib_sub_le (n : ℕ) :
    (F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) := by
  sorry

/-- Equality in `KTFib.sq_fib_sub_le` holds, for `n ≥ 1`, exactly when `n = 1`. -/
theorem sq_fib_sub_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    (F (2 * n + 1) - t ^ n) ^ 2 = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) ↔
      n = 1 := by
  sorry

end CrossFamily

end KTFib
