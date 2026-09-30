/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.MeanInequalities.Converse
public import Mathlib.Analysis.MeanInequalities.PowerSum
public import Mathlib.NumberTheory.KTFibonacci.Identities

/-!
# Hölder-type inequalities for `(k, t)`-Lucas numbers

Let `k, t` be real numbers and let `L` be the `(k, t)`-Lucas sequence: `L 0 = 2`, `L 1 = k` and
`L (n + 2) = k * L (n + 1) + t * L n`. This file proves `(k, t)` versions of the Hölder-type
inequalities that Batte and Kaggwa prove for the `k`-Lucas numbers (the case `t = 1`).

Sums run over `i ∈ Finset.Icc 1 n`. For weights `w i` we write `S γ = ∑ i, w i * L i ^ γ`
(real powers `γ`) and `W = ∑ i, w i`. Two families of weights are used.

* `w i = t ^ (n - i)`, for `t ≥ 1` (or `t ≥ 0` in the converse inequalities). For these weights
  the sum of squares telescopes: `S 2 = D` with `D = (L n * L (n + 1) - 2 * k * t ^ n) / k`
  (`KTFib.sum_pow_mul_rpow_two_lucas`). At `t = 1` all weights are `1`.
* `w i = t⁻¹ ^ (i - 1)`, for `0 < t ≤ 1`. These are the weights `t ^ (n - i)` divided by their
  smallest value `t ^ (n - 1)`, so `1 ≤ w i` and `S 2 = D / t ^ (n - 1)`
  (`KTFib.sum_inv_pow_mul_rpow_two_lucas`).

The statements write out `D` (and the other closed forms) in full.

## Main results

* `KTFib.holder_sandwich_of_one_lt_of_two_le`, `KTFib.holder_sandwich_of_one_lt_of_lt_two`,
  `KTFib.holder_sandwich_of_lt_one_of_two_le`, `KTFib.holder_sandwich_of_lt_one_of_lt_two`
  (Batte–Kaggwa, Theorem 1.2, for `t = 1`): for `w i = t ^ (n - i)` with `t ≥ 1`, chains of
  inequalities comparing `S α`, `α = u / p + v / q`, with the Hölder bound
  `S u ^ (1 / p) * S v ^ (1 / q)` and with `D`, `D ^ (α / 2)` and `W ^ (1 - α / 2) * D ^ (α / 2)`,
  according to whether `p > 1` or `0 < p < 1`, and `α ≥ 2` or `α < 2`.
* `KTFib.holder_sandwich_inv_of_one_lt_of_two_le`, ...: the same four chains for
  `w i = t⁻¹ ^ (i - 1)` with `0 < t ≤ 1`, with `D` replaced by `D / t ^ (n - 1)`.
* `KTFib.converse_holder_lucas_of_one_lt`, `KTFib.converse_holder_lucas_of_lt_one`
  (Theorem 1.3): for `w i = t ^ (n - i)`, `u / p + v / q = 2` and `L i ^ ((u - v) / p) ∈ [m, M]`
  with `0 < m < M`, the linear and the multiplicative converse Hölder inequalities between
  `S u`, `S v` and `D`. `KTFib.lucas_rpow_bounds` shows that the values of `L i ^ ((u - v) / p)`
  at `i = 1` and `i = n` are admissible bounds `m`, `M`.
* `KTFib.converse_cauchy_lucas` (Theorem 1.4): the converse Cauchy–Schwarz inequalities for
  the power sums of `x i = L i * L (i + 1)` with weights `t ^ (n - i)`.

The corresponding statements for arbitrary weighted power sums are in
`Mathlib.Analysis.MeanInequalities.PowerSum` and `Mathlib.Analysis.MeanInequalities.Converse`;
Dujella, Jakšetić and Pečarić apply them to the Fibonacci numbers.

## References

* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
* [A. Dujella, J. Jakšetić and J. Pečarić, *Fibonacci numbers and Hölder inequality*]
  [dujella_jaksetic_pecaric]
-/

public section

open Finset

namespace KTFib

variable {k t : ℝ} {L : ℕ → ℝ}

/-! ### The weighted sums of squares -/

/-- For `k ≠ 0`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ (2 : ℝ) = (L n * L (n + 1) - 2 * k * t ^ n) / k`. -/
theorem sum_pow_mul_rpow_two_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ (2 : ℝ) = (L n * L (n + 1) - 2 * k * t ^ n) / k := by
  simp_rw [Real.rpow_two]
  exact sum_pow_mul_sq_lucas hk hL0 hL1 hL n

/-- For `k ≠ 0` and `t ≠ 0`, `∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ (2 : ℝ) =
(L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))`. -/
theorem sum_inv_pow_mul_rpow_two_lucas (hk : k ≠ 0) (ht : t ≠ 0) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ (2 : ℝ) =
      (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1)) := by
  rw [← div_div, ← sum_pow_mul_rpow_two_lucas hk hL0 hL1 hL, sum_div]
  refine sum_congr rfl fun i hi ↦ ?_
  obtain ⟨h1, h2⟩ := mem_Icc.1 hi
  rw [show n - 1 = n - i + (i - 1) by omega, pow_add, inv_pow]
  field_simp

/-- `1 ≤ L i` for `i ∈ Icc 1 n`, if `1 ≤ k` and `0 ≤ t`. -/
private lemma one_le_lucas_of_mem_Icc (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} : ∀ i ∈ Icc 1 n, 1 ≤ L i :=
  fun _ hi ↦ one_le_lucas hk ht hL0 hL1 hL (mem_Icc.1 hi).1

/-! ### Hölder sandwiches for `t ≥ 1` (Theorem 1.2) -/

/-- **Hölder sandwich, `p > 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(i), for `t = 1`). Let
`1 ≤ k`, `1 ≤ t`, let `p`, `q` be conjugate exponents and `α = u / p + v / q ≥ 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ`, `W = ∑ i ∈ Icc 1 n, t ^ (n - i)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`,
`W ^ (1 - α / 2) * D ^ (α / 2) ≤ S α`, `D ≤ W ^ (1 - α / 2) * D ^ (α / 2)` and
`S α ^ (2 / α) ≤ D`. -/
theorem holder_sandwich_of_one_lt_of_two_le (hk : 1 ≤ k) (ht : 1 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} {p q u v α : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      (L n * L (n + 1) - 2 * k * t ^ n) / k ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α) ^ (2 / α) ≤
        (L n * L (n + 1) - 2 * k * t ^ n) / k := by
  have hx := one_le_lucas_of_mem_Icc hk (zero_le_one.trans ht) hL0 hL1 hL (n := n)
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t ^ (n - i) := fun _ _ ↦ one_le_pow₀ ht
  have hw0 : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun i hi ↦ zero_le_one.trans (hw i hi)
  have hx0 : ∀ i ∈ Icc 1 n, 0 ≤ L i := fun i hi ↦ zero_le_one.trans (hx i hi)
  rw [← sum_pow_mul_rpow_two_lucas (by positivity) hL0 hL1 hL]
  exact ⟨Real.sum_mul_rpow_le_of_one_lt _ hpq hα hw0 fun i hi ↦ one_pos.trans_le (hx i hi),
    Real.rpow_mean_le_of_le _ two_pos h2α hw0 hx0,
    Real.sum_le_rpow_mean_of_one_le _ two_pos h2α hw0 hx,
    Real.sum_rpow_rpow_le_of_le _ two_pos h2α hw hx0⟩

/-- **Hölder sandwich, `p > 1`, `0 ≤ α < 2`** (Batte–Kaggwa, Theorem 1.2(ii), for `t = 1`). Let
`0 < k`, `1 ≤ t`, `1 ≤ n`, let `p`, `q` be conjugate exponents and `0 ≤ α = u / p + v / q < 2`.
Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` and
`D ^ (α / 2) ≤ S α`. -/
theorem holder_sandwich_of_one_lt_of_lt_two (hk : 0 < k) (ht : 1 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 1 ≤ n)
    {p q u v α : ℝ} (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (hα0 : 0 ≤ α)
    (hα2 : α < 2) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ∧
      ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α := by
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk (by positivity) hL0 hL1 hL i
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t ^ (n - i) := fun _ _ ↦ one_le_pow₀ ht
  rw [← sum_pow_mul_rpow_two_lucas hk.ne' hL0 hL1 hL]
  exact ⟨Real.sum_mul_rpow_le_of_one_lt _ hpq hα (fun i hi ↦ zero_le_one.trans (hw i hi)) hx,
    Real.rpow_le_sum_rpow_of_le _ (nonempty_Icc.2 hn) hα0 hα2.le two_pos hw
      fun i hi ↦ (hx i hi).le⟩

/-- **Hölder sandwich, `0 < p < 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(iii), for `t = 1`). Let
`0 < k`, `1 ≤ t`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `α = u / p + v / q ≥ 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and `D = (L n * L (n + 1) - 2 * k * t ^ n) / k`.
Then `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α` and `S α ≤ D ^ (α / 2)`. -/
theorem holder_sandwich_of_lt_one_of_two_le (hk : 0 < k) (ht : 1 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} {p q u v α : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) := by
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk (by positivity) hL0 hL1 hL i
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t ^ (n - i) := fun _ _ ↦ one_le_pow₀ ht
  rw [← sum_pow_mul_rpow_two_lucas hk.ne' hL0 hL1 hL]
  exact ⟨Real.le_sum_mul_rpow_of_lt_one _ hp0 hp1 hpq hα
      (fun i hi ↦ zero_le_one.trans (hw i hi)) hx,
    Real.sum_rpow_le_rpow_of_le _ two_pos h2α hw fun i hi ↦ (hx i hi).le⟩

/-- **Hölder sandwich, `0 < p < 1`, `0 < α < 2`** (Batte–Kaggwa, Theorem 1.2(iv), for `t = 1`).
Let `1 ≤ k`, `1 ≤ t`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `0 < α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ`, `W = ∑ i ∈ Icc 1 n, t ^ (n - i)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`,
`S α ≤ W ^ (1 - α / 2) * D ^ (α / 2)`, `W ^ (1 - α / 2) * D ^ (α / 2) ≤ D` and
`D ≤ S α ^ (2 / α)`. -/
theorem holder_sandwich_of_lt_one_of_lt_two (hk : 1 ≤ k) (ht : 1 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} {p q u v α : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α)
    (hα2 : α < 2) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) ≤
        (L n * L (n + 1) - 2 * k * t ^ n) / k ∧
      (L n * L (n + 1) - 2 * k * t ^ n) / k ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α) ^ (2 / α) := by
  have hx := one_le_lucas_of_mem_Icc hk (zero_le_one.trans ht) hL0 hL1 hL (n := n)
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t ^ (n - i) := fun _ _ ↦ one_le_pow₀ ht
  have hw0 : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun i hi ↦ zero_le_one.trans (hw i hi)
  have hx0 : ∀ i ∈ Icc 1 n, 0 ≤ L i := fun i hi ↦ zero_le_one.trans (hx i hi)
  rw [← sum_pow_mul_rpow_two_lucas (by positivity) hL0 hL1 hL]
  exact ⟨Real.le_sum_mul_rpow_of_lt_one _ hp0 hp1 hpq hα hw0
      fun i hi ↦ one_pos.trans_le (hx i hi),
    Real.le_rpow_mean_of_le _ hα0 hα2.le hw0 hx0,
    Real.rpow_mean_le_sum_of_one_le _ hα0 hα2.le hw0 hx,
    Real.sum_rpow_le_rpow_of_le _ hα0 hα2.le hw hx0⟩

/-! ### Hölder sandwiches for `0 < t ≤ 1`

For `t < 1` the weights `t ^ (n - i)` are smaller than `1`, and the norm comparisons in the
chains above fail. Dividing the weights by their smallest value `t ^ (n - 1)` gives the weights
`t⁻¹ ^ (i - 1) ≥ 1`, and the same chains hold with `D` replaced by `D / t ^ (n - 1)`. -/

/-- **Hölder sandwich for `0 < t ≤ 1`, `p > 1`, `α ≥ 2`.** Let `1 ≤ k`, `0 < t ≤ 1`, let `p`,
`q` be conjugate exponents and `α = u / p + v / q ≥ 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ γ`, `W = ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))`. Then
`S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`, `W ^ (1 - α / 2) * D ^ (α / 2) ≤ S α`,
`D ≤ W ^ (1 - α / 2) * D ^ (α / 2)` and `S α ^ (2 / α) ≤ D`. -/
theorem holder_sandwich_inv_of_one_lt_of_two_le (hk : 1 ≤ k) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ}
    {p q u v α : ℝ} (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ∧
      (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ∧
      (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1)) ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α) ^ (2 / α) ≤
        (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1)) := by
  have hx := one_le_lucas_of_mem_Icc hk ht0.le hL0 hL1 hL (n := n)
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t⁻¹ ^ (i - 1) := fun _ _ ↦ one_le_pow₀ ((one_le_inv₀ ht0).2 ht1)
  have hw0 : ∀ i ∈ Icc 1 n, 0 ≤ t⁻¹ ^ (i - 1) := fun i hi ↦ zero_le_one.trans (hw i hi)
  have hx0 : ∀ i ∈ Icc 1 n, 0 ≤ L i := fun i hi ↦ zero_le_one.trans (hx i hi)
  rw [← sum_inv_pow_mul_rpow_two_lucas (by positivity) ht0.ne' hL0 hL1 hL]
  exact ⟨Real.sum_mul_rpow_le_of_one_lt _ hpq hα hw0 fun i hi ↦ one_pos.trans_le (hx i hi),
    Real.rpow_mean_le_of_le _ two_pos h2α hw0 hx0,
    Real.sum_le_rpow_mean_of_one_le _ two_pos h2α hw0 hx,
    Real.sum_rpow_rpow_le_of_le _ two_pos h2α hw hx0⟩

/-- **Hölder sandwich for `0 < t ≤ 1`, `p > 1`, `0 ≤ α < 2`.** Let `0 < k`, `0 < t ≤ 1`,
`1 ≤ n`, let `p`, `q` be conjugate exponents and `0 ≤ α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))`. Then
`S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` and `D ^ (α / 2) ≤ S α`. -/
theorem holder_sandwich_inv_of_one_lt_of_lt_two (hk : 0 < k) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ}
    (hn : 1 ≤ n) {p q u v α : ℝ} (hpq : p.HolderConjugate q) (hα : u / p + v / q = α)
    (hα0 : 0 ≤ α) (hα2 : α < 2) :
    ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ∧
      ((L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α := by
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk ht0.le hL0 hL1 hL i
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t⁻¹ ^ (i - 1) := fun _ _ ↦ one_le_pow₀ ((one_le_inv₀ ht0).2 ht1)
  rw [← sum_inv_pow_mul_rpow_two_lucas hk.ne' ht0.ne' hL0 hL1 hL]
  exact ⟨Real.sum_mul_rpow_le_of_one_lt _ hpq hα (fun i hi ↦ zero_le_one.trans (hw i hi)) hx,
    Real.rpow_le_sum_rpow_of_le _ (nonempty_Icc.2 hn) hα0 hα2.le two_pos hw
      fun i hi ↦ (hx i hi).le⟩

/-- **Hölder sandwich for `0 < t ≤ 1`, `0 < p < 1`, `α ≥ 2`.** Let `0 < k`, `0 < t ≤ 1`,
`0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `α = u / p + v / q ≥ 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))`. Then
`S u ^ (1 / p) * S v ^ (1 / q) ≤ S α` and `S α ≤ D ^ (α / 2)`. -/
theorem holder_sandwich_inv_of_lt_one_of_two_le (hk : 0 < k) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ}
    {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α)
    (h2α : 2 ≤ α) :
    (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        ((L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) ^ (α / 2) := by
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk ht0.le hL0 hL1 hL i
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t⁻¹ ^ (i - 1) := fun _ _ ↦ one_le_pow₀ ((one_le_inv₀ ht0).2 ht1)
  rw [← sum_inv_pow_mul_rpow_two_lucas hk.ne' ht0.ne' hL0 hL1 hL]
  exact ⟨Real.le_sum_mul_rpow_of_lt_one _ hp0 hp1 hpq hα
      (fun i hi ↦ zero_le_one.trans (hw i hi)) hx,
    Real.sum_rpow_le_rpow_of_le _ two_pos h2α hw fun i hi ↦ (hx i hi).le⟩

/-- **Hölder sandwich for `0 < t ≤ 1`, `0 < p < 1`, `0 < α < 2`.** Let `1 ≤ k`, `0 < t ≤ 1`,
`0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `0 < α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ γ`, `W = ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))`. Then
`S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`, `S α ≤ W ^ (1 - α / 2) * D ^ (α / 2)`,
`W ^ (1 - α / 2) * D ^ (α / 2) ≤ D` and `D ≤ S α ^ (2 / α)`. -/
theorem holder_sandwich_inv_of_lt_one_of_lt_two (hk : 1 ≤ k) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ}
    {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α)
    (hα0 : 0 < α) (hα2 : α < 2) :
    (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1)) ^ (1 - α / 2) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1))) ^ (α / 2) ≤
        (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1)) ∧
      (L n * L (n + 1) - 2 * k * t ^ n) / (k * t ^ (n - 1)) ≤
        (∑ i ∈ Icc 1 n, t⁻¹ ^ (i - 1) * L i ^ α) ^ (2 / α) := by
  have hx := one_le_lucas_of_mem_Icc hk ht0.le hL0 hL1 hL (n := n)
  have hw : ∀ i ∈ Icc 1 n, 1 ≤ t⁻¹ ^ (i - 1) := fun _ _ ↦ one_le_pow₀ ((one_le_inv₀ ht0).2 ht1)
  have hw0 : ∀ i ∈ Icc 1 n, 0 ≤ t⁻¹ ^ (i - 1) := fun i hi ↦ zero_le_one.trans (hw i hi)
  have hx0 : ∀ i ∈ Icc 1 n, 0 ≤ L i := fun i hi ↦ zero_le_one.trans (hx i hi)
  rw [← sum_inv_pow_mul_rpow_two_lucas (by positivity) ht0.ne' hL0 hL1 hL]
  exact ⟨Real.le_sum_mul_rpow_of_lt_one _ hp0 hp1 hpq hα hw0
      fun i hi ↦ one_pos.trans_le (hx i hi),
    Real.le_rpow_mean_of_le _ hα0 hα2.le hw0 hx0,
    Real.rpow_mean_le_sum_of_one_le _ hα0 hα2.le hw0 hx,
    Real.sum_rpow_le_rpow_of_le _ hα0 hα2.le hw hx0⟩

/-! ### Converse Hölder inequalities (Theorem 1.3) -/

/-- **Converse Hölder inequalities for `(k, t)`-Lucas numbers, `p > 1`** (Batte–Kaggwa,
Theorem 1.3, for `t = 1`). Let `0 < k`, `0 ≤ t`, let `p`, `q` be conjugate exponents with
`u / p + v / q = 2`, and let `0 < m < M` with `L i ^ ((u - v) / p) ∈ [m, M]` for
`i ∈ Icc 1 n`. Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * D` and
`S u ^ (1 / p) * S v ^ (1 / q) ≤
(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D`.
See `KTFib.lucas_rpow_bounds` for admissible `m` and `M`. -/
theorem converse_holder_lucas_of_one_lt (hk : 0 < k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} {p q u v m M : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = 2) (hm : 0 < m) (hmM : m < M)
    (hr : ∀ i ∈ Icc 1 n, L i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M - m) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u +
          (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v ≤
        (M ^ p - m ^ p) * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) := by
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk ht hL0 hL1 hL i
  rw [← sum_pow_mul_rpow_two_lucas hk.ne' hL0 hL1 hL]
  exact ⟨Real.converse_holder_linear_of_one_lt _ hpq hα hw hx hm.le hr,
    Real.converse_holder_of_one_lt _ hpq hα hw hx hm hmM hr⟩

/-- **Converse Hölder inequalities for `(k, t)`-Lucas numbers, `0 < p < 1`** (Batte–Kaggwa,
Theorem 1.3, for `t = 1`). Let `0 < k`, `0 ≤ t`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1`,
`u / p + v / q = 2`, and let `0 < m < M` with `L i ^ ((u - v) / p) ∈ [m, M]` for
`i ∈ Icc 1 n`. Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then
`(M ^ p - m ^ p) * D ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v` and
`(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D ≤
S u ^ (1 / p) * S v ^ (1 / q)`. See `KTFib.lucas_rpow_bounds` for admissible `m` and `M`. -/
theorem converse_holder_lucas_of_lt_one (hk : 0 < k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} {p q u v m M : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = 2) (hm : 0 < m)
    (hmM : m < M) (hr : ∀ i ∈ Icc 1 n, L i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ≤
        (M - m) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u +
          (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v ∧
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) := by
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk ht hL0 hL1 hL i
  rw [← sum_pow_mul_rpow_two_lucas hk.ne' hL0 hL1 hL]
  exact ⟨Real.converse_holder_linear_of_lt_one _ hp0 hp1 hpq hα hw hx hm.le hr,
    Real.converse_holder_of_lt_one _ hp0 hp1 hpq hα hw hx hm hmM hr⟩

/-- For `1 ≤ k`, `0 < t`, `2 ≤ n` and `e ≠ 0`, the smaller and the larger of `L 1 ^ e` and
`L n ^ e`, `m = min (L 1 ^ e) (L n ^ e)` and `M = max (L 1 ^ e) (L n ^ e)`, satisfy `0 < m < M`,
and `L i ^ e ∈ [m, M]` for every `i ∈ Icc 1 n`. -/
theorem lucas_rpow_bounds (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 2 ≤ n) {e : ℝ} (he : e ≠ 0) :
    0 < min (L 1 ^ e) (L n ^ e) ∧ min (L 1 ^ e) (L n ^ e) < max (L 1 ^ e) (L n ^ e) ∧
      ∀ i ∈ Icc 1 n, L i ^ e ∈ Set.Icc (min (L 1 ^ e) (L n ^ e)) (max (L 1 ^ e) (L n ^ e)) := by
  have hpos := lucas_pos (zero_lt_one.trans_le hk) ht.le hL0 hL1 hL
  have hmono := lucas_monotoneOn hk ht.le hL0 hL1 hL
  have h1n : L 1 < L n := lucas_strictMonoOn hk ht hL0 hL1 hL Set.self_mem_Ici
    (show 1 ≤ n by omega) (by omega)
  refine ⟨lt_min (Real.rpow_pos_of_pos (hpos 1) e) (Real.rpow_pos_of_pos (hpos n) e),
    min_lt_max.2 fun h ↦ h1n.ne ((Real.rpow_left_inj (hpos 1).le (hpos n).le he).1 h),
    fun i hi ↦ Real.rpow_mem_Icc_min_max e (hpos 1) ⟨?_, ?_⟩⟩
  · exact hmono Set.self_mem_Ici (mem_Icc.1 hi).1 (mem_Icc.1 hi).1
  · exact hmono (mem_Icc.1 hi).1 (show 1 ≤ n by omega) (mem_Icc.1 hi).2

/-! ### Converse Cauchy–Schwarz inequalities (Theorem 1.4) -/

/-- If `0 ≤ m₁ ≤ a ≤ M₁` and `0 < m₂ ≤ b ≤ M₂`, then `m₁ / M₂ * b ≤ a ≤ M₁ / m₂ * b`. -/
private lemma div_mul_le_and_le_div_mul {a b m₁ M₁ m₂ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂)
    (ha : a ∈ Set.Icc m₁ M₁) (hb : b ∈ Set.Icc m₂ M₂) : m₁ / M₂ * b ≤ a ∧ a ≤ M₁ / m₂ * b := by
  have hM₂ : 0 < M₂ := hm₂.trans_le (hb.1.trans hb.2)
  have hM₁ : 0 ≤ M₁ := hm₁.trans (ha.1.trans ha.2)
  constructor
  · calc m₁ / M₂ * b ≤ m₁ / M₂ * M₂ := by gcongr; exact hb.2
      _ = m₁ := div_mul_cancel₀ _ hM₂.ne'
      _ ≤ a := ha.1
  · calc a ≤ M₁ := ha.2
      _ = M₁ / m₂ * m₂ := (div_mul_cancel₀ _ hm₂.ne').symm
      _ ≤ M₁ / m₂ * b := by gcongr; exact hb.1

/-- The Pólya–Szegő constant for the ratio bounds `m₁ / M₂` and `M₁ / m₂`. -/
private lemma sqrt_add_sqrt_sq_div_four {m₁ M₁ m₂ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : 0 < M₁)
    (hm₂ : 0 < m₂) (hM₂ : 0 < M₂) :
    (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 =
      (m₁ / M₂ + M₁ / m₂) ^ 2 / (4 * (m₁ / M₂) * (M₁ / m₂)) := by
  have h1 : √(M₁ * M₂ / (m₁ * m₂)) * √(m₁ * m₂ / (M₁ * M₂)) = 1 := by
    rw [← Real.sqrt_mul (by positivity),
      show M₁ * M₂ / (m₁ * m₂) * (m₁ * m₂ / (M₁ * M₂)) = 1 by field_simp, Real.sqrt_one]
  rw [add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), mul_assoc, h1]
  field_simp
  ring

/-- **Converse Cauchy–Schwarz inequalities for `x i = L i * L (i + 1)`** (Batte–Kaggwa,
Theorem 1.4, for `t = 1`). Let `1 ≤ k`, `0 ≤ t`, `1 ≤ n` and `u + v = 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * x i ^ γ` and `W = ∑ i ∈ Icc 1 n, t ^ (n - i)`. The
hypotheses `hm₁`, ..., `hP` name the quantities involved: `m₁`, `M₁` are the smaller and the
larger of `x 1 ^ (u / 2)` and `x n ^ (u / 2)`, `m₂`, `M₂` those of `x 1 ^ (v / 2)` and
`x n ^ (v / 2)`, and `P = S 1` in closed form. Then
* `1 ≤ S u * S v / P ^ 2 ≤ (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4`;
* `S u / P - P / S v ≤ (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2`;
* `S u * S v - P ^ 2 ≤ W ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2`;
* `S v + m₂ * M₂ / (M₁ * m₁) * S u ≤ (M₂ / m₁ + m₂ / M₁) * P`. -/
theorem converse_cauchy_lucas (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 1 ≤ n)
    {u v m₁ M₁ m₂ M₂ P : ℝ} (huv : u + v = 2)
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
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hx0 : ∀ i, 0 < L i * L (i + 1) := fun i ↦
    mul_pos (lucas_pos hk0 ht hL0 hL1 hL i) (lucas_pos hk0 ht hL0 hL1 hL (i + 1))
  have hmono := lucas_mul_lucas_succ_monotoneOn hk ht hL0 hL1 hL
  have hx : ∀ i ∈ Icc 1 n, L i * L (i + 1) ∈ Set.Icc (L 1 * L 2) (L n * L (n + 1)) :=
    fun i hi ↦ ⟨hmono Set.self_mem_Ici (mem_Icc.1 hi).1 (mem_Icc.1 hi).1,
      hmono (mem_Icc.1 hi).1 (hn.trans le_rfl) (mem_Icc.1 hi).2⟩
  have ha : ∀ i ∈ Icc 1 n, (L i * L (i + 1)) ^ (u / 2) ∈ Set.Icc m₁ M₁ := fun i hi ↦ by
    rw [hm₁, hM₁]; exact Real.rpow_mem_Icc_min_max _ (hx0 1) (hx i hi)
  have hb : ∀ i ∈ Icc 1 n, (L i * L (i + 1)) ^ (v / 2) ∈ Set.Icc m₂ M₂ := fun i hi ↦ by
    rw [hm₂, hM₂]; exact Real.rpow_mem_Icc_min_max _ (hx0 1) (hx i hi)
  have hnI : n ∈ Icc 1 n := mem_Icc.2 ⟨hn, le_rfl⟩
  have hmin (e : ℝ) : 0 < min ((L 1 * L 2) ^ e) ((L n * L (n + 1)) ^ e) :=
    lt_min (Real.rpow_pos_of_pos (hx0 1) e) (Real.rpow_pos_of_pos (hx0 n) e)
  have hm₁0 : 0 < m₁ := hm₁ ▸ hmin _
  have hm₂0 : 0 < m₂ := hm₂ ▸ hmin _
  have hM₁0 : 0 < M₁ := hm₁0.trans_le ((ha n hnI).1.trans (ha n hnI).2)
  have hM₂0 : 0 < M₂ := hm₂0.trans_le ((hb n hnI).1.trans (hb n hnI).2)
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  -- a weighted sum of positive terms is positive, thanks to the term `i = n` of weight `1`
  have hsum_pos (f : ℕ → ℝ) (hf : ∀ i, 0 < f i) : 0 < ∑ i ∈ Icc 1 n, t ^ (n - i) * f i :=
    sum_pos' (fun i hi ↦ mul_nonneg (hw i hi) (hf i).le)
      ⟨n, hnI, by rw [Nat.sub_self, pow_zero, one_mul]; exact hf n⟩
  have hsq (e : ℝ) : ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ e =
      ∑ i ∈ Icc 1 n, t ^ (n - i) * ((L i * L (i + 1)) ^ (e / 2)) ^ 2 :=
    sum_congr rfl fun i _ ↦ by
      rw [← Real.rpow_mul_natCast (hx0 i).le]; norm_num
  have hP' : P = ∑ i ∈ Icc 1 n, t ^ (n - i) * ((L i * L (i + 1)) ^ (u / 2) *
      (L i * L (i + 1)) ^ (v / 2)) := by
    rw [hP, ← sum_pow_mul_lucas_mul_succ hk0.ne' hL0 hL1 hL]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← Real.rpow_add (hx0 i), ← add_div, huv, div_self two_ne_zero, Real.rpow_one]
  have hB := hsum_pos _ fun i ↦ pow_pos (Real.rpow_pos_of_pos (hx0 i) (v / 2)) 2
  have hC := hsum_pos _ fun i ↦ mul_pos (Real.rpow_pos_of_pos (hx0 i) (u / 2))
    (Real.rpow_pos_of_pos (hx0 i) (v / 2))
  have hr := fun i hi ↦ div_mul_le_and_le_div_mul hm₁0.le hm₂0 (ha i hi) (hb i hi)
  have hr' := fun i hi ↦ div_mul_le_and_le_div_mul hm₂0.le hm₁0 (hb i hi) (ha i hi)
  have hoz := Real.ozeki_rpow (Icc 1 n) (y := fun i ↦ L i * L (i + 1)) (σ := u / 2) (τ := v / 2)
    hw (hx0 1) hx
  rw [← hm₁, ← hM₁, ← hm₂, ← hM₂] at hoz
  rw [hsq u, hsq v, hP']
  refine ⟨⟨(one_le_div (pow_pos hC 2)).2 <| sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _))
      (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _)) fun i _ ↦ le_of_eq (by ring), ?_⟩,
    Real.shisha_mond _ hw (by positivity) (by positivity) (fun i hi ↦ (hr i hi).1)
      (fun i hi ↦ (hr i hi).2) hC hB, hoz, ?_⟩
  · rw [div_le_iff₀ (pow_pos hC 2), sqrt_add_sqrt_sq_div_four hm₁0 hM₁0 hm₂0 hM₂0]
    exact polya_szego hw (by positivity) (by positivity) (fun i hi ↦ (hr i hi).1)
      fun i hi ↦ (hr i hi).2
  · have h := diaz_metcalf hw (fun i hi ↦ (hr' i hi).1) fun i hi ↦ (hr' i hi).2
    rw [div_mul_div_comm, add_comm (m₂ / M₁)] at h
    simpa only [mul_comm ((L _ * L (_ + 1)) ^ (v / 2))] using h

end KTFib
