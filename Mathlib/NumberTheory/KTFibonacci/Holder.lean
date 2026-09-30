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
  rw [eq_div_iff hk, mul_comm, mul_sum_sq hL, hL0, hL1]
  ring

/-- `∑ i ∈ [1, n], t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k`. -/
theorem sum_sq_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_sq hF, hF0, hF1]
  ring

/-- `∑ i ∈ [1, n], t ^ (n - i) * (L i * L (i + 1))` in closed form. -/
theorem sum_lucas_mul_succ (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
      (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k := by
  have h2 : L 2 = k * L 1 + t * L 0 := hL 0
  have h := two_mul_mul_sum_mul_succ hL n
  rw [h2, hL0, hL1] at h
  rw [eq_div_iff hk]
  linear_combination h / 2

/-- `∑ i ∈ [1, n], F i = (F (n + 1) + t * F n - 1) / (k + t - 1)`. -/
theorem sum_fib (hkt : k + t ≠ 1) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i = (F (n + 1) + t * F n - 1) / (k + t - 1) := by
  rw [eq_div_iff (sub_ne_zero.2 hkt), mul_comm, mul_sum hF, hF0, hF1]
  ring

/-- `∑ i ∈ [1, n], L i = (L (n + 1) + t * L n - k - 2 * t) / (k + t - 1)`. -/
theorem sum_lucas (hkt : k + t ≠ 1) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i = (L (n + 1) + t * L n - k - 2 * t) / (k + t - 1) := by
  rw [eq_div_iff (sub_ne_zero.2 hkt), mul_comm, mul_sum hL, hL0, hL1]
  ring

/-- `∑ i ∈ [1, n], t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k`. -/
theorem sum_fib_odd (hk : k ≠ 0) (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_odd hF, hF0]
  ring

/-- `∑ i ∈ [1, n], t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k`. -/
theorem sum_fib_even (hk : k ≠ 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_even hF, hF1]
  ring

/-- `∑ i ∈ [1, n], t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k`. -/
theorem sum_lucas_odd (hk : k ≠ 0) (hL0 : L 0 = 2) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_odd hL, hL0]
  ring

/-- `∑ i ∈ [1, n], t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k`. -/
theorem sum_lucas_even (hk : k ≠ 0) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_even hL, hL1]
  ring

private lemma sum_rpow_two_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ (2 : ℝ) = (L n * L (n + 1) - 2 * k * t ^ n) / k := by
  simp_rw [Real.rpow_two]
  exact sum_sq_lucas hk hL0 hL1 hL n

private lemma sandwich_hw (ht : 1 ≤ t) {n : ℕ} : ∀ i ∈ Icc 1 n, 1 ≤ t ^ (n - i) :=
  fun _ _ ↦ one_le_pow₀ ht

private lemma sandwich_hx (hk : 1 ≤ k) (ht : 1 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} : ∀ i ∈ Icc 1 n, 1 ≤ L i :=
  fun _ hi ↦ one_le_lucas hk (by linarith) hL0 hL1 hL (mem_Icc.1 hi).1

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
  obtain ⟨h1, h2, h3, h4⟩ := Real.powerSum_chain_of_one_lt_of_le (Icc 1 n) (β := 2) hp hpq hα
    two_pos h2α (nonempty_Icc.2 hn) (sandwich_hw ht) (sandwich_hx hk ht hL0 hL1 hL)
  rw [sum_rpow_two_lucas (by linarith) hL0 hL1 hL, ← hD] at h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- **Hölder sandwich, `p > 1`, `0 ≤ α < 2`.** -/
theorem holder_sandwich_of_one_lt_of_lt_two {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ∧
      D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α := by
  obtain ⟨h1, h2⟩ := Real.powerSum_chain_of_one_lt_of_lt (Icc 1 n) (β := 2) hp hpq hα hα0 hα2
    (nonempty_Icc.2 hn) (sandwich_hw ht)
    (fun i hi ↦ one_pos.trans_le (sandwich_hx hk ht hL0 hL1 hL i hi))
  rw [sum_rpow_two_lucas (by linarith) hL0 hL1 hL, ← hD] at h2
  exact ⟨h1, h2⟩

/-- **Hölder sandwich, `0 < p < 1`, `α ≥ 2`.** -/
theorem holder_sandwich_of_lt_one_of_two_le {n : ℕ} {p q u v α D : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / k) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤ D ^ (α / 2) := by
  obtain ⟨h1, h2⟩ := Real.powerSum_chain_of_lt_one_of_le (Icc 1 n) (β := 2) hp0 hp1 hpq hα
    two_pos h2α (sandwich_hw ht)
    (fun i hi ↦ one_pos.trans_le (sandwich_hx hk ht hL0 hL1 hL i hi))
  rw [sum_rpow_two_lucas (by linarith) hL0 hL1 hL, ← hD] at h2
  exact ⟨h1, h2⟩

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
  obtain ⟨h1, h2, h3, h4⟩ := Real.powerSum_chain_of_lt_one_of_lt (Icc 1 n) (β := 2) hp0 hp1 hpq
    hα hα0 hα2 (nonempty_Icc.2 hn) (sandwich_hw ht) (sandwich_hx hk ht hL0 hL1 hL)
  rw [sum_rpow_two_lucas (by linarith) hL0 hL1 hL, ← hD] at h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end Sandwich

/-! ### Hölder sandwiches for `0 < t ≤ 1`

For `t < 1` the weights `t ^ (n - i)` are smaller than `1`, and the norm comparisons of the
chains fail.  Dividing them by their smallest value `t ^ (n - 1)` gives the weights
`t⁻¹ ^ (i - 1) ≥ 1`, and the same chains hold with `D` replaced by `D / t ^ (n - 1)`. -/

section SandwichSmall

private lemma sum_rpow_two_lucas_inv (hk : k ≠ 0) (ht : t ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ (2 : ℝ) =
      (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1)) := by
  have key : ∀ i ∈ Icc 1 n,
      t⁻¹ ^ (i - 1) * L i ^ (2 : ℝ) = t ^ (n - i) * L i ^ (2 : ℝ) / t ^ (n - 1) := by
    intro i hi
    obtain ⟨h1, h2⟩ := mem_Icc.1 hi
    have hsplit : t ^ (n - 1) = t ^ (n - i) * t ^ (i - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, inv_pow]
    field_simp
  rw [sum_congr rfl key, ← sum_div, sum_rpow_two_lucas hk hL0 hL1 hL, div_div]

private lemma sandwich_hw_inv (ht0 : 0 < t) (ht1 : t ≤ 1) {n : ℕ} :
    ∀ i ∈ Icc 1 n, 1 ≤ t⁻¹ ^ (i - 1) :=
  fun _ _ ↦ one_le_pow₀ ((one_le_inv₀ ht0).2 ht1)

variable (hk : 1 ≤ k) (ht0 : 0 < t) (ht1 : t ≤ 1) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht0 ht1 hL0 hL1 hL

omit ht1 in
private lemma sandwich_hx' {n : ℕ} : ∀ i ∈ Icc 1 n, 1 ≤ L i :=
  fun _ hi ↦ one_le_lucas hk ht0 hL0 hL1 hL (mem_Icc.1 hi).1

/-- **Hölder sandwich, `0 < t ≤ 1`, `p > 1`, `α ≥ 2`**, with weights `t⁻¹ ^ (i - 1)`. -/
theorem holder_sandwich_of_one_lt_of_two_le_of_le_one {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) :
    ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ∧
      (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) * D ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ∧
      D ≤ (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) * D ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α) ^ (2 / α) ≤ D := by
  obtain ⟨h1, h2, h3, h4⟩ := Real.powerSum_chain_of_one_lt_of_le (Icc 1 n) (β := 2) hp hpq hα
    two_pos h2α (nonempty_Icc.2 hn) (sandwich_hw_inv ht0 ht1)
    (sandwich_hx' hk ht0 hL0 hL1 hL)
  rw [sum_rpow_two_lucas_inv (by linarith) ht0.ne' hL0 hL1 hL, ← hD] at h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- **Hölder sandwich, `0 < t ≤ 1`, `p > 1`, `0 ≤ α < 2`**, with weights `t⁻¹ ^ (i - 1)`. -/
theorem holder_sandwich_of_one_lt_of_lt_two_of_le_one {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) :
    ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ∧
      D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α := by
  obtain ⟨h1, h2⟩ := Real.powerSum_chain_of_one_lt_of_lt (Icc 1 n) (β := 2) hp hpq hα hα0 hα2
    (nonempty_Icc.2 hn) (sandwich_hw_inv ht0 ht1)
    (fun i hi ↦ one_pos.trans_le (sandwich_hx' hk ht0 hL0 hL1 hL i hi))
  rw [sum_rpow_two_lucas_inv (by linarith) ht0.ne' hL0 hL1 hL, ← hD] at h2
  exact ⟨h1, h2⟩

/-- **Hölder sandwich, `0 < t ≤ 1`, `0 < p < 1`, `α ≥ 2`**, with weights `t⁻¹ ^ (i - 1)`. -/
theorem holder_sandwich_of_lt_one_of_two_le_of_le_one {n : ℕ} {p q u v α D : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) :
    (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤ D ^ (α / 2) := by
  obtain ⟨h1, h2⟩ := Real.powerSum_chain_of_lt_one_of_le (Icc 1 n) (β := 2) hp0 hp1 hpq hα
    two_pos h2α (sandwich_hw_inv ht0 ht1)
    (fun i hi ↦ one_pos.trans_le (sandwich_hx' hk ht0 hL0 hL1 hL i hi))
  rw [sum_rpow_two_lucas_inv (by linarith) ht0.ne' hL0 hL1 hL, ← hD] at h2
  exact ⟨h1, h2⟩

/-- **Hölder sandwich, `0 < t ≤ 1`, `0 < p < 1`, `0 < α < 2`**, with weights
`t⁻¹ ^ (i - 1)`. -/
theorem holder_sandwich_of_lt_one_of_lt_two_of_le_one {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α)
    (hα2 : α < 2) (hD : D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) :
    (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) * D ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) * D ^ (α / 2) ≤ D ∧
      D ≤ (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α) ^ (2 / α) := by
  obtain ⟨h1, h2, h3, h4⟩ := Real.powerSum_chain_of_lt_one_of_lt (Icc 1 n) (β := 2) hp0 hp1 hpq
    hα hα0 hα2 (nonempty_Icc.2 hn) (sandwich_hw_inv ht0 ht1) (sandwich_hx' hk ht0 hL0 hL1 hL)
  rw [sum_rpow_two_lucas_inv (by linarith) ht0.ne' hL0 hL1 hL, ← hD] at h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end SandwichSmall

/-! ### Converse Hölder refinements (Theorem 1.3) -/

section ConverseHolder

variable (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht hL0 hL1 hL

private lemma converse_bounds {n : ℕ} (hn : 2 ≤ n) {e m M : ℝ} (he : e ≠ 0)
    (hm : m = min (L 1 ^ e) (L n ^ e)) (hM : M = max (L 1 ^ e) (L n ^ e)) :
    0 < m ∧ m < M ∧ ∀ i ∈ Icc 1 n, m ≤ L i ^ e ∧ L i ^ e ≤ M := by
  have hpos : ∀ i, 0 < L i := lucas_pos (by linarith) ht hL0 hL1 hL
  have h1n : L 1 < L n := lucas_strictMono hk ht hL0 hL1 hL le_rfl (by omega)
  subst hm hM
  refine ⟨lt_min (Real.rpow_pos_of_pos (hpos 1) e) (Real.rpow_pos_of_pos (hpos n) e),
    min_lt_max.2 ?_, fun i hi ↦ ?_⟩
  · rcases he.lt_or_gt with he | he
    · exact (Real.rpow_lt_rpow_of_neg (hpos 1) h1n he).ne'
    · exact (Real.rpow_lt_rpow (hpos 1).le h1n he).ne
  · obtain ⟨h1i, hin⟩ := mem_Icc.1 hi
    have hl : L 1 ≤ L i := lucas_mono hk ht hL0 hL1 hL le_rfl h1i
    have hr : L i ≤ L n := lucas_mono hk ht hL0 hL1 hL h1i hin
    rcases le_total 0 e with he | he
    · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow (hpos 1).le hl he),
        (Real.rpow_le_rpow (hpos i).le hr he).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hpos i) hr he),
        (Real.rpow_le_rpow_of_nonpos (hpos 1) hl he).trans (le_max_left _ _)⟩

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
  have he : (u - v) / p ≠ 0 := div_ne_zero (sub_ne_zero.2 huv) (zero_lt_one.trans hp).ne'
  obtain ⟨hm0, hmM, hr⟩ := converse_bounds hk ht hL0 hL1 hL hn he hm hM
  have hw : ∀ i ∈ Icc 1 n, (0 : ℝ) ≤ t ^ (n - i) := fun i _ ↦ by positivity
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos (by linarith) ht hL0 hL1 hL i
  have h1 := Real.converse_holder_linear_of_one_lt (Icc 1 n) hp hpq hα hw hx hm0 hr
  have h2 := Real.converse_holder_of_one_lt (Icc 1 n) hp hpq hα hw hx hm0 hmM hr
  rw [sum_rpow_two_lucas (by linarith) hL0 hL1 hL, ← hD] at h1 h2
  exact ⟨hm0, hmM, h1, h2⟩

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
  have he : (u - v) / p ≠ 0 := div_ne_zero (sub_ne_zero.2 huv) hp0.ne'
  obtain ⟨hm0, hmM, hr⟩ := converse_bounds hk ht hL0 hL1 hL hn he hm hM
  have hw : ∀ i ∈ Icc 1 n, (0 : ℝ) < t ^ (n - i) := fun i _ ↦ by positivity
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos (by linarith) ht hL0 hL1 hL i
  have h1 := Real.converse_holder_linear_of_lt_one (Icc 1 n) hp0 hp1 hpq hα
    (fun i hi ↦ (hw i hi).le) hx hm0 hr
  have h2 := Real.converse_holder_of_lt_one (Icc 1 n) hp0 hp1 hpq hα
    (nonempty_Icc.2 (by omega)) hw hx hm0 hmM hr
  rw [sum_rpow_two_lucas (by linarith) hL0 hL1 hL, ← hD] at h1 h2
  exact ⟨hm0, hmM, h1, h2⟩

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
  have hk0 : 0 < k := by linarith
  have hpos := lucas_pos hk0 ht hL0 hL1 hL
  have hα : u / 2 + v / 2 = 1 := by linarith
  have hw : ∀ i ∈ Icc 1 n, (0 : ℝ) < t ^ (n - i) := fun i _ ↦ by positivity
  have hx : ∀ i ∈ Icc 1 n,
      L 1 * L 2 ≤ L i * L (i + 1) ∧ L i * L (i + 1) ≤ L n * L (n + 1) := fun i hi ↦
    ⟨lucas_mul_mono hk ht hL0 hL1 hL le_rfl (mem_Icc.1 hi).1,
      lucas_mul_mono hk ht hL0 hL1 hL (mem_Icc.1 hi).1 (mem_Icc.1 hi).2⟩
  have h := Real.cauchy_conversion (Icc 1 n) (x := fun i ↦ L i * L (i + 1)) hα
    (nonempty_Icc.2 hn) hw (mul_pos (hpos 1) (hpos 2)) hx hm₁ hM₁ hm₂ hM₂
  have hS : ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ (1 : ℝ) = P := by
    simp_rw [Real.rpow_one]
    rw [hP]
    exact sum_lucas_mul_succ hk0.ne' hL0 hL1 hL n
  beta_reduce at h
  rw [hS] at h
  exact h

end CauchyConversion

/-- Weighted Lagrange identity. -/
private lemma weighted_lagrange {ι : Type*} (s : Finset ι) (w a b : ι → ℝ) :
    2 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) -
        (∑ i ∈ s, w i * (a i * b i)) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 := by
  have h1 := sum_mul_sum s s (fun i ↦ w i * a i ^ 2) (fun i ↦ w i * b i ^ 2)
  have h2 : (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w j * a j ^ 2 * (w i * b i ^ 2) := by
    rw [sum_comm, sum_mul_sum]
  have h3 : (∑ i ∈ s, w i * (a i * b i)) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, w i * (a i * b i) * (w j * (a j * b j)) := by
    rw [sq, sum_mul_sum]
  rw [mul_sub, two_mul, h3]
  nth_rewrite 1 [h1]
  rw [h2, Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ ↦ by ring

/-! ### The cross-family bound (Theorem 1.5) -/

section CrossFamily

variable (hk : 0 < k) (ht : 0 < t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
  (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
  (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
include hk ht hF0 hF1 hF hL0 hL1 hL

omit ht in
private lemma cross_eq (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = ∑ i ∈ Icc 1 n, t ^ (n - i) * (F i * L i) ∧
      F n * F (n + 1) / k = ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 ∧
      (L n * L (n + 1) - 2 * k * t ^ n) / k = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 :=
  ⟨sum_congr rfl fun i _ ↦ by rw [fib_mul_lucas hF0 hF1 hF hL0 hL1 hL i],
    (sum_sq_fib hk.ne' hF0 hF1 hF n).symm, (sum_sq_lucas hk.ne' hL0 hL1 hL n).symm⟩

/-- **Cross-family Cauchy–Schwarz bound.** -/
theorem sq_sum_fib_two_mul_le (n : ℕ) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
      F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) := by
  obtain ⟨e1, e2, e3⟩ := cross_eq hk hF0 hF1 hF hL0 hL1 hL n
  rw [e1, e2, e3]
  have h := weighted_lagrange (Icc 1 n) (fun i ↦ t ^ (n - i)) F L
  beta_reduce at h
  have hnn : 0 ≤ ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n,
      t ^ (n - i) * t ^ (n - j) * (F i * L j - F j * L i) ^ 2 :=
    sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ by positivity
  linarith

/-- **Equality case of the cross-family bound**: for `n ≥ 1`, equality holds exactly when
`n = 1`. -/
theorem sq_sum_fib_two_mul_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
        F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ↔ n = 1 := by
  have hF2 : F 2 = k * F 1 + t * F 0 := hF 0
  have hL2 : L 2 = k * L 1 + t * L 0 := hL 0
  rw [hF0, hF1] at hF2
  rw [hL0, hL1] at hL2
  constructor
  · intro heq
    by_contra h1
    have hn2 : 2 ≤ n := by omega
    obtain ⟨e1, e2, e3⟩ := cross_eq hk hF0 hF1 hF hL0 hL1 hL n
    rw [e1, e2, e3] at heq
    have h := weighted_lagrange (Icc 1 n) (fun i ↦ t ^ (n - i)) F L
    beta_reduce at h
    have hpos : 0 < ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n,
        t ^ (n - i) * t ^ (n - j) * (F i * L j - F j * L i) ^ 2 := by
      refine sum_pos' (fun i _ ↦ sum_nonneg fun j _ ↦ by positivity)
        ⟨1, mem_Icc.2 ⟨le_rfl, hn⟩, ?_⟩
      refine sum_pos' (fun j _ ↦ by positivity) ⟨2, mem_Icc.2 ⟨by norm_num, hn2⟩, ?_⟩
      have : F 1 * L 2 - F 2 * L 1 = 2 * t := by rw [hF1, hF2, hL2, hL1]; ring
      rw [this]
      positivity
    linarith
  · rintro rfl
    simp only [Icc_self, sum_singleton, Nat.sub_self, pow_zero, one_mul, mul_one, pow_one]
    rw [show 1 + 1 = 2 from rfl, hF1, hF2, hL2, hL1]
    field_simp
    ring

/-- **The cross-family bound in closed form**:
`(F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)`. -/
theorem sq_fib_sub_le (n : ℕ) :
    (F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) := by
  have h := sq_sum_fib_two_mul_le hk ht hF0 hF1 hF hL0 hL1 hL n
  rw [sum_fib_even hk.ne' hF1 hF n] at h
  calc (F (2 * n + 1) - t ^ n) ^ 2 = k ^ 2 * ((F (2 * n + 1) - t ^ n) / k) ^ 2 := by
        field_simp
    _ ≤ k ^ 2 * (F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)) := by gcongr
    _ = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) := by
        field_simp

/-- Equality in `KTFib.sq_fib_sub_le` holds, for `n ≥ 1`, exactly when `n = 1`. -/
theorem sq_fib_sub_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    (F (2 * n + 1) - t ^ n) ^ 2 = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) ↔
      n = 1 := by
  rw [← sq_sum_fib_two_mul_eq_iff hk ht hF0 hF1 hF hL0 hL1 hL hn, sum_fib_even hk.ne' hF1 hF n,
    div_pow, div_mul_div_comm, ← sq, div_left_inj' (by positivity)]

end CrossFamily

end KTFib
