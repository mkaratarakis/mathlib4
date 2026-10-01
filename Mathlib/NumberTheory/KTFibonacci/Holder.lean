/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.MeanInequalities.Converse
public import Mathlib.NumberTheory.KTFibonacci.Identities

/-!
# Hölder-type inequalities for `(k, t)`-Lucas numbers

Let `k, t` be real numbers and let `L` be the `(k, t)`-Lucas sequence: `L 0 = 2`, `L 1 = k` and
`L (n + 2) = k * L (n + 1) + t * L n`. This file proves `(k, t)` versions of the Hölder-type
inequalities that Batte and Kaggwa prove for the `k`-Lucas numbers (the case `t = 1`), and states
their results at `t = 1`.

Sums run over `i ∈ Finset.Icc 1 n`, with the weights `w i = t ^ (n - i)` for `t ≥ 0`. We write
`S γ = ∑ i, t ^ (n - i) * L i ^ γ` (real powers `γ`) and `W = ∑ i, t ^ (n - i)`. For these
weights the sum of squares telescopes: `S 2 = D` with `D = (L n * L (n + 1) - 2 * k * t ^ n) / k`
(`KTFib.sum_pow_mul_lucas_sq`). The statements write out `D` (and the other closed forms) in full.
At `t = 1` all weights are `1` and `W = n`.

The comparisons of weighted `ℓ^γ` norms in `Mathlib.Analysis.MeanInequalities.PowerSum` need
every `L i ^ 2` to be at most `S 2`. This holds for `1 ≤ k` because the term `i = n` of `S 2` has
weight `1` and `L` is increasing (`KTFib.lucas_sq_le_sum_pow_mul_lucas_sq`), and it holds for
`1 ≤ t` because then every weight is at least `1`.

## Main results

* `KTFib.holder_lucas_of_one_lt_of_two_le`, `KTFib.holder_lucas_of_one_lt_of_lt_two`,
  `KTFib.holder_lucas_of_lt_one_of_two_le`, `KTFib.holder_lucas_of_lt_one_of_lt_two`
  (Batte–Kaggwa, Theorem 1.2, for `t = 1`): for `t ≥ 0`, chains of inequalities comparing
  `S α`, `α = u / p + v / q`, with the Hölder bound `S u ^ (1 / p) * S v ^ (1 / q)` and with `D`,
  `D ^ (α / 2)` and `W ^ (1 - α / 2) * D ^ (α / 2)`, according to whether `p > 1` or
  `0 < p < 1`, and `α ≥ 2` or `α < 2`.
* `KTFib.converse_holder_lucas_of_one_lt_of_mem_Icc`,
  `KTFib.converse_holder_lucas_of_lt_one_of_mem_Icc` (Theorem 1.3): for `u / p + v / q = 2` and
  bounds `L i ^ ((u - v) / p) ∈ [m, M]` with `0 < m < M`, the linear and the multiplicative
  converse Hölder inequalities between `S u`, `S v` and `D`.
* `KTFib.converse_holder_lucas_of_one_lt`, `KTFib.converse_holder_lucas_of_lt_one`: the same with
  `m`, `M` the smaller and the larger of the endpoint values `L 1 ^ ((u - v) / p)` and
  `L n ^ ((u - v) / p)`. These bound every `L i ^ ((u - v) / p)` (`KTFib.lucas_rpow_mem_uIcc`),
  and `0 < m < M` holds when `0 < t`, `2 ≤ n` and `u ≠ v` (`KTFib.min_lucas_rpow_pos`,
  `KTFib.min_lucas_rpow_lt_max`).
* `KTFib.converse_cauchy_schwarz_lucas_mul_lucas_succ` (Theorem 1.4): the converse Cauchy–Schwarz
  inequalities for the power sums of `x i = L i * L (i + 1)` with weights `t ^ (n - i)`; see
  `KTFib.lucas_mul_lucas_succ_rpow_mem_uIcc` for the bounds.
* `KFib.holder_lucas_of_one_lt_of_two_le`, ..., `KFib.converse_cauchy_schwarz_lucas_mul_lucas_succ`:
  the results of Batte and Kaggwa, i.e. the case `t = 1`, where `W = n`.

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

/-- `S 2 = D`: for `k ≠ 0`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ (2 : ℝ) = (L n * L (n + 1) - 2 * k * t ^ n) / k`. -/
private lemma sum_pow_mul_rpow_two_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ (2 : ℝ) = (L n * L (n + 1) - 2 * k * t ^ n) / k := by
  simp_rw [Real.rpow_two]
  exact sum_pow_mul_lucas_sq hk hL0 hL1 hL n

/-- Every `L i ^ 2`, `i ∈ Icc 1 n`, is at most `S 2`, if `1 ≤ k` or `1 ≤ t`. -/
private lemma rpow_two_le_sum_pow_mul_rpow_two (ht : 0 ≤ t) (hkt : 1 ≤ k ∨ 1 ≤ t)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} :
    ∀ i ∈ Icc 1 n, L i ^ (2 : ℝ) ≤ ∑ j ∈ Icc 1 n, t ^ (n - j) * L j ^ (2 : ℝ) := by
  intro i hi
  simp only [Real.rpow_two]
  obtain hk | ht1 := hkt
  · exact lucas_sq_le_sum_pow_mul_lucas_sq hk ht hL0 hL1 hL hi
  · calc L i ^ 2 ≤ t ^ (n - i) * L i ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ht1)
      _ ≤ _ := single_le_sum (f := fun j ↦ t ^ (n - j) * L j ^ 2)
          (fun j _ ↦ mul_nonneg (pow_nonneg ht _) (sq_nonneg _)) hi

/-- `W ≤ S 2`, if `1 ≤ k` and `0 ≤ t`. -/
private lemma sum_pow_le_sum_pow_mul_rpow_two (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} :
    ∑ i ∈ Icc 1 n, t ^ (n - i) ≤ ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ (2 : ℝ) :=
  sum_le_sum fun _ hi ↦ le_mul_of_one_le_right (pow_nonneg ht _)
    (Real.one_le_rpow (one_le_lucas hk ht hL0 hL1 hL (mem_Icc.1 hi).1) zero_le_two)

/-! ### Hölder-type chains (Theorem 1.2) -/

/-- **Hölder-type chain, `p > 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(i), for `t = 1`). Let
`1 ≤ k`, `0 ≤ t`, let `p`, `q` be conjugate exponents and `α = u / p + v / q ≥ 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ`, `W = ∑ i ∈ Icc 1 n, t ^ (n - i)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`,
`W ^ (1 - α / 2) * D ^ (α / 2) ≤ S α`, `D ≤ W ^ (1 - α / 2) * D ^ (α / 2)` and
`S α ^ (2 / α) ≤ D`. -/
theorem holder_lucas_of_one_lt_of_two_le (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
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
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk0 ht hL0 hL1 hL i
  have hx0 : ∀ i ∈ Icc 1 n, 0 ≤ L i := fun i hi ↦ (hx i hi).le
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (Real.rpow_nonneg (hx0 i hi) _)
  rw [← sum_pow_mul_rpow_two_lucas hk0.ne' hL0 hL1 hL]
  refine ⟨Real.sum_mul_rpow_le_Lp_mul_Lq_of_one_lt _ hpq hα hw hx,
    Real.weight_mul_Lp_le_sum_mul_rpow _ two_pos h2α hw hx0, ?_, ?_⟩
  · obtain hW | hW := (sum_nonneg hw).eq_or_lt
    · -- all weights vanish
      rw [sum_mul_eq_zero_of_sum_eq_zero hw hW.symm, ← hW]
      positivity
    exact Real.le_rpow_one_sub_mul_rpow_of_le hW (sum_pow_le_sum_pow_mul_rpow_two hk ht hL0 hL1 hL)
      ((one_le_div two_pos).2 h2α)
  -- `S α ≤ S 2 ^ (α / 2)`, raised to the power `2 / α`
  rw [← inv_div, Real.rpow_inv_le_iff_of_pos (hS α) (hS 2) (by positivity)]
  exact Real.sum_mul_rpow_le_rpow_sum_mul_rpow _ two_pos h2α hw hx0
    (rpow_two_le_sum_pow_mul_rpow_two ht (.inl hk) hL0 hL1 hL)

/-- **Hölder-type chain, `p > 1`, `α < 2`** (Batte–Kaggwa, Theorem 1.2(ii), for `t = 1`). Let
`0 < k`, `0 ≤ t` with `1 ≤ k` or `1 ≤ t`, let `1 ≤ n`, let `p`, `q` be conjugate exponents and
`α = u / p + v / q < 2`. Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` and
`D ^ (α / 2) ≤ S α`. -/
theorem holder_lucas_of_one_lt_of_lt_two (hk : 0 < k) (ht : 0 ≤ t) (hkt : 1 ≤ k ∨ 1 ≤ t)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ}
    (hn : 1 ≤ n) {p q u v α : ℝ} (hpq : p.HolderConjugate q) (hα : u / p + v / q = α)
    (hα2 : α < 2) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ∧
      ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α := by
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk ht hL0 hL1 hL i
  have hS2 := rpow_two_le_sum_pow_mul_rpow_two ht hkt hL0 hL1 hL (n := n)
  have hnI : n ∈ Icc 1 n := mem_Icc.2 ⟨hn, le_rfl⟩
  rw [← sum_pow_mul_rpow_two_lucas hk.ne' hL0 hL1 hL]
  exact ⟨Real.sum_mul_rpow_le_Lp_mul_Lq_of_one_lt _ hpq hα hw hx,
    Real.rpow_sum_mul_rpow_le_sum_mul_rpow _ hα2.le two_pos hw (fun i hi ↦ (hx i hi).le) hS2
      ((Real.rpow_pos_of_pos (hx n hnI) 2).trans_le (hS2 n hnI))⟩

/-- **Hölder-type chain, `0 < p < 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(iii), for `t = 1`). Let
`0 < k`, `0 ≤ t` with `1 ≤ k` or `1 ≤ t`, let `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and
`α = u / p + v / q ≥ 2`. Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α` and
`S α ≤ D ^ (α / 2)`. -/
theorem holder_lucas_of_lt_one_of_two_le (hk : 0 < k) (ht : 0 ≤ t) (hkt : 1 ≤ k ∨ 1 ≤ t)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ}
    {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α)
    (h2α : 2 ≤ α) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ α ≤
        ((L n * L (n + 1) - 2 * k * t ^ n) / k) ^ (α / 2) := by
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk ht hL0 hL1 hL i
  rw [← sum_pow_mul_rpow_two_lucas hk.ne' hL0 hL1 hL]
  exact ⟨Real.Lp_mul_Lq_le_sum_mul_rpow_of_lt_one _ hp0 hp1 hpq hα hw hx,
    Real.sum_mul_rpow_le_rpow_sum_mul_rpow _ two_pos h2α hw (fun i hi ↦ (hx i hi).le)
      (rpow_two_le_sum_pow_mul_rpow_two ht hkt hL0 hL1 hL)⟩

/-- **Hölder-type chain, `0 < p < 1`, `0 < α < 2`** (Batte–Kaggwa, Theorem 1.2(iv), for `t = 1`).
Let `1 ≤ k`, `0 ≤ t`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `0 < α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ`, `W = ∑ i ∈ Icc 1 n, t ^ (n - i)` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`,
`S α ≤ W ^ (1 - α / 2) * D ^ (α / 2)`, `W ^ (1 - α / 2) * D ^ (α / 2) ≤ D` and
`D ≤ S α ^ (2 / α)`. -/
theorem holder_lucas_of_lt_one_of_lt_two (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
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
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hx : ∀ i ∈ Icc 1 n, 0 < L i := fun i _ ↦ lucas_pos hk0 ht hL0 hL1 hL i
  have hx0 : ∀ i ∈ Icc 1 n, 0 ≤ L i := fun i hi ↦ (hx i hi).le
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (Real.rpow_nonneg (hx0 i hi) _)
  rw [← sum_pow_mul_rpow_two_lucas hk0.ne' hL0 hL1 hL]
  refine ⟨Real.Lp_mul_Lq_le_sum_mul_rpow_of_lt_one _ hp0 hp1 hpq hα hw hx,
    Real.sum_mul_rpow_le_weight_mul_Lp _ hα0 hα2.le hw hx0,
    Real.rpow_one_sub_mul_rpow_le_of_le (sum_nonneg hw)
      (sum_pow_le_sum_pow_mul_rpow_two hk ht hL0 hL1 hL) ((div_le_one two_pos).2 hα2.le), ?_⟩
  -- `S 2 ^ (α / 2) ≤ S α`, raised to the power `2 / α`
  obtain hS2 | hS2 := (hS 2).eq_or_lt
  · rw [← hS2]
    exact Real.rpow_nonneg (hS α) _
  rw [← inv_div, Real.le_rpow_inv_iff_of_pos (hS 2) (hS α) (by positivity)]
  exact Real.rpow_sum_mul_rpow_le_sum_mul_rpow _ hα2.le two_pos hw hx0
    (rpow_two_le_sum_pow_mul_rpow_two ht (.inl hk) hL0 hL1 hL) hS2

/-! ### Converse Hölder inequalities (Theorem 1.3) -/

/-- **Converse Hölder inequalities for `(k, t)`-Lucas numbers, `p > 1`**, for arbitrary bounds
(Batte–Kaggwa, Theorem 1.3, for `t = 1`). Let `0 < k`, `0 ≤ t`, let `p`, `q` be conjugate
exponents with `u / p + v / q = 2`, and let `0 < m < M` bound every `L i ^ ((u - v) / p)`,
`i ∈ Icc 1 n`. Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * D` and
`S u ^ (1 / p) * S v ^ (1 / q) ≤
(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D`.
`KTFib.converse_holder_lucas_of_one_lt` takes for `m`, `M` the endpoint values. -/
theorem converse_holder_lucas_of_one_lt_of_mem_Icc (hk : 0 < k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
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
  exact ⟨Real.converse_holder_linear_rpow_of_one_lt _ hpq hα hw hx hm.le hr,
    Real.converse_holder_rpow_of_one_lt _ hpq hα hw hx hm hmM hr⟩

/-- **Converse Hölder inequalities for `(k, t)`-Lucas numbers, `0 < p < 1`**, for arbitrary
bounds (Batte–Kaggwa, Theorem 1.3, for `t = 1`). Let `0 < k`, `0 ≤ t`, `0 < p < 1`,
`p⁻¹ + q⁻¹ = 1`, `u / p + v / q = 2`, and let `0 < m < M` bound every `L i ^ ((u - v) / p)`,
`i ∈ Icc 1 n`. Write `S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k * t ^ n) / k`. Then
`(M ^ p - m ^ p) * D ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v` and
`(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D ≤
S u ^ (1 / p) * S v ^ (1 / q)`. `KTFib.converse_holder_lucas_of_lt_one` takes for `m`, `M` the
endpoint values. -/
theorem converse_holder_lucas_of_lt_one_of_mem_Icc (hk : 0 < k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
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
  exact ⟨Real.converse_holder_linear_rpow_of_lt_one _ hp0 hp1 hpq hα hw hx hm.le hr,
    Real.converse_holder_rpow_of_lt_one _ hp0 hp1 hpq hα hw hx hm hmM hr⟩

/-- For `1 ≤ k` and `0 ≤ t`, `L i ^ e` lies between `L 1 ^ e` and `L n ^ e` for every
`i ∈ Icc 1 n`. -/
theorem lucas_rpow_mem_uIcc (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i n : ℕ} (hi : i ∈ Icc 1 n) (e : ℝ) :
    L i ^ e ∈ Set.uIcc (L 1 ^ e) (L n ^ e) := by
  have hpos := lucas_pos (zero_lt_one.trans_le hk) ht hL0 hL1 hL
  exact Real.rpow_mem_uIcc e (hpos 1) (hpos n)
    (Set.Icc_subset_uIcc (lucas_mem_Icc hk ht hL0 hL1 hL hi))

/-- For `1 ≤ k` and `0 ≤ t`, `(L i * L (i + 1)) ^ e` lies between `(L 1 * L 2) ^ e` and
`(L n * L (n + 1)) ^ e` for every `i ∈ Icc 1 n`. -/
theorem lucas_mul_lucas_succ_rpow_mem_uIcc (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i n : ℕ} (hi : i ∈ Icc 1 n)
    (e : ℝ) : (L i * L (i + 1)) ^ e ∈ Set.uIcc ((L 1 * L 2) ^ e) ((L n * L (n + 1)) ^ e) := by
  have hpos := lucas_pos (zero_lt_one.trans_le hk) ht hL0 hL1 hL
  exact Real.rpow_mem_uIcc e (mul_pos (hpos 1) (hpos 2)) (mul_pos (hpos n) (hpos (n + 1)))
    (Set.Icc_subset_uIcc (lucas_mul_lucas_succ_mem_Icc hk ht hL0 hL1 hL hi))

/-- For `0 < k` and `0 ≤ t`, the smaller of `L 1 ^ e` and `L n ^ e` is positive. -/
theorem min_lucas_rpow_pos (hk : 0 < k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) (e : ℝ) :
    0 < min (L 1 ^ e) (L n ^ e) :=
  lt_min (Real.rpow_pos_of_pos (lucas_pos hk ht hL0 hL1 hL 1) e)
    (Real.rpow_pos_of_pos (lucas_pos hk ht hL0 hL1 hL n) e)

/-- For `1 ≤ k`, `0 < t`, `2 ≤ n` and `e ≠ 0`, the smaller of `L 1 ^ e` and `L n ^ e` is smaller
than the larger one. -/
theorem min_lucas_rpow_lt_max (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 2 ≤ n) {e : ℝ} (he : e ≠ 0) :
    min (L 1 ^ e) (L n ^ e) < max (L 1 ^ e) (L n ^ e) := by
  have hpos := lucas_pos (zero_lt_one.trans_le hk) ht.le hL0 hL1 hL
  have h1n : L 1 < L n := lucas_strictMonoOn hk ht hL0 hL1 hL Set.self_mem_Ici
    (show 1 ≤ n by omega) (by omega)
  exact min_lt_max.2 fun h ↦ h1n.ne ((Real.rpow_left_inj (hpos 1).le (hpos n).le he).1 h)

/-- **Converse Hölder inequalities for `(k, t)`-Lucas numbers, `p > 1`** (Batte–Kaggwa,
Theorem 1.3, for `t = 1`). Let `1 ≤ k`, `0 < t`, `2 ≤ n`, let `p`, `q` be conjugate exponents
with `u / p + v / q = 2` and `u ≠ v`, and let `m`, `M` be the smaller and the larger of
`L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)` (hypotheses `hm`, `hM`); they bound every
`L i ^ ((u - v) / p)`, `i ∈ Icc 1 n` (`KTFib.lucas_rpow_mem_uIcc`). Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and `D = (L n * L (n + 1) - 2 * k * t ^ n) / k`.
Then `0 < m < M` (`KTFib.min_lucas_rpow_pos`, `KTFib.min_lucas_rpow_lt_max`),
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * D` and
`S u ^ (1 / p) * S v ^ (1 / q) ≤
(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D`. -/
theorem converse_holder_lucas_of_one_lt (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 2 ≤ n)
    {p q u v m M : ℝ} (hpq : p.HolderConjugate q) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p))) :
    0 < m ∧ m < M ∧
      (M - m) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u +
          (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v ≤
        (M ^ p - m ^ p) * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ∧
      (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) ≤
        (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) := by
  subst hm hM
  have hm0 := min_lucas_rpow_pos (zero_lt_one.trans_le hk) ht.le hL0 hL1 hL n ((u - v) / p)
  have hmM := min_lucas_rpow_lt_max hk ht hL0 hL1 hL hn
    (div_ne_zero (sub_ne_zero.2 huv) hpq.ne_zero)
  exact ⟨hm0, hmM, converse_holder_lucas_of_one_lt_of_mem_Icc (zero_lt_one.trans_le hk) ht.le
    hL0 hL1 hL hpq hα hm0 hmM fun i hi ↦ by
      rw [Set.Icc_min_max]; exact lucas_rpow_mem_uIcc hk ht.le hL0 hL1 hL hi _⟩

/-- **Converse Hölder inequalities for `(k, t)`-Lucas numbers, `0 < p < 1`** (Batte–Kaggwa,
Theorem 1.3, for `t = 1`). Let `1 ≤ k`, `0 < t`, `2 ≤ n`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1`,
`u / p + v / q = 2` and `u ≠ v`, and let `m`, `M` be the smaller and the larger of
`L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)` (hypotheses `hm`, `hM`); they bound every
`L i ^ ((u - v) / p)`, `i ∈ Icc 1 n` (`KTFib.lucas_rpow_mem_uIcc`). Write
`S γ = ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ γ` and `D = (L n * L (n + 1) - 2 * k * t ^ n) / k`.
Then `0 < m < M` (`KTFib.min_lucas_rpow_pos`, `KTFib.min_lucas_rpow_lt_max`),
`(M ^ p - m ^ p) * D ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v` and
`(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D ≤
S u ^ (1 / p) * S v ^ (1 / q)`. -/
theorem converse_holder_lucas_of_lt_one (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 2 ≤ n)
    {p q u v m M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p))) :
    0 < m ∧ m < M ∧
      (M ^ p - m ^ p) * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ≤
        (M - m) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u +
          (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v ∧
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          ((L n * L (n + 1) - 2 * k * t ^ n) / k) ≤
        (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ u) ^ (1 / p) *
          (∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ v) ^ (1 / q) := by
  subst hm hM
  have hm0 := min_lucas_rpow_pos (zero_lt_one.trans_le hk) ht.le hL0 hL1 hL n ((u - v) / p)
  have hmM := min_lucas_rpow_lt_max hk ht hL0 hL1 hL hn (div_ne_zero (sub_ne_zero.2 huv) hp0.ne')
  exact ⟨hm0, hmM, converse_holder_lucas_of_lt_one_of_mem_Icc (zero_lt_one.trans_le hk) ht.le
    hL0 hL1 hL hp0 hp1 hpq hα hm0 hmM fun i hi ↦ by
      rw [Set.Icc_min_max]; exact lucas_rpow_mem_uIcc hk ht.le hL0 hL1 hL hi _⟩

/-! ### Converse Cauchy–Schwarz inequalities (Theorem 1.4) -/

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
theorem converse_cauchy_schwarz_lucas_mul_lucas_succ (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 1 ≤ n)
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
  have hpos := lucas_pos hk0 ht hL0 hL1 hL
  have hx0 : ∀ i, 0 < L i * L (i + 1) := fun i ↦ mul_pos (hpos i) (hpos (i + 1))
  have hy : ∀ i ∈ Icc 1 n, 0 < L i * L (i + 1) := fun i _ ↦ hx0 i
  have hw : ∀ i ∈ Icc 1 n, 0 ≤ t ^ (n - i) := fun _ _ ↦ pow_nonneg ht _
  have hmem (e : ℝ) : ∀ i ∈ Icc 1 n, (L i * L (i + 1)) ^ e ∈
      Set.Icc (min ((L 1 * L 2) ^ e) ((L n * L (n + 1)) ^ e))
        (max ((L 1 * L 2) ^ e) ((L n * L (n + 1)) ^ e)) := fun i hi ↦ by
    rw [Set.Icc_min_max]
    exact lucas_mul_lucas_succ_rpow_mem_uIcc hk ht hL0 hL1 hL hi e
  have ha := hmem (u / 2)
  have hb := hmem (v / 2)
  rw [← hm₁, ← hM₁] at ha
  rw [← hm₂, ← hM₂] at hb
  have hm₁0 : 0 < m₁ := hm₁ ▸ lt_min (Real.rpow_pos_of_pos (mul_pos (hpos 1) (hpos 2)) _)
    (Real.rpow_pos_of_pos (hx0 n) _)
  have hm₂0 : 0 < m₂ := hm₂ ▸ lt_min (Real.rpow_pos_of_pos (mul_pos (hpos 1) (hpos 2)) _)
    (Real.rpow_pos_of_pos (hx0 n) _)
  have hnI : n ∈ Icc 1 n := mem_Icc.2 ⟨hn, le_rfl⟩
  have hP' : P = ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ ((u + v) / 2) := by
    rw [hP, ← sum_pow_mul_lucas_mul_lucas_succ hk0.ne' hL0 hL1 hL, huv, div_self two_ne_zero]
    simp only [Real.rpow_one]
  have hPpos : 0 < ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) ^ ((u + v) / 2) :=
    sum_pos' (fun i hi ↦ mul_nonneg (hw i hi) (Real.rpow_nonneg (hx0 i).le _))
      ⟨n, hnI, by rw [Nat.sub_self, pow_zero, one_mul]; exact Real.rpow_pos_of_pos (hx0 n) _⟩
  subst hP'
  refine ⟨⟨(one_le_div (pow_pos hPpos 2)).2 (Real.sq_sum_mul_rpow_add_div_two_le _ hw hy),
    (div_le_iff₀ (pow_pos hPpos 2)).2 (Real.polya_szego_rpow _ hw hy hm₁0 hm₂0 ha hb)⟩,
    Real.shisha_mond_rpow _ hw hy hm₁0.le hm₂0 ha hb, ?_,
    Real.diaz_metcalf_rpow _ hw hy hm₁0 hm₂0.le ha hb⟩
  have hoz := Real.ozeki_rpow (Icc 1 n) (y := fun i ↦ L i * L (i + 1)) (u := u) (v := v) hw
    (mul_pos (hpos 1) (hpos 2)) fun i hi ↦ lucas_mul_lucas_succ_mem_Icc hk ht hL0 hL1 hL hi
  rwa [← hm₁, ← hM₁, ← hm₂, ← hM₂] at hoz

end KTFib

/-! ### The `k`-Lucas numbers: the results of Batte and Kaggwa

At `t = 1` the weights `t ^ (n - i)` are all `1` and the total weight is `n`. Throughout,
`D = (L n * L (n + 1) - 2 * k) / k` is the `D_k(n)` of Batte and Kaggwa and
`P = L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2)` is their `P_k(n)`. They take `k`
to be a positive integer; here `k` is real with `k > 0` (Theorem 1.2(ii), (iii)) or `k ≥ 1`
(Theorem 1.2(i), (iv), Theorems 1.3 and 1.4). -/

namespace KFib

variable {k : ℝ} {L : ℕ → ℝ}

/-- At `t = 1` the total weight is `n`. -/
private lemma sum_one (n : ℕ) : ∑ _i ∈ Icc 1 n, (1 : ℝ) = n := by
  simp

/-- `n ^ (1 - α / 2) = 1 / n ^ (α / 2 - 1)`, the form used by Batte and Kaggwa. -/
private lemma rpow_one_sub (n : ℕ) (α : ℝ) :
    (n : ℝ) ^ (1 - α / 2) = 1 / (n : ℝ) ^ (α / 2 - 1) := by
  rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n), neg_sub]

/-- **Hölder-type chain, `p > 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(i)). Let `1 ≤ k`, let `p`,
`q` be conjugate exponents and `α = u / p + v / q ≥ 2`. Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k) / k`. Then `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`,
`1 / n ^ (α / 2 - 1) * D ^ (α / 2) ≤ S α`, `D ≤ 1 / n ^ (α / 2 - 1) * D ^ (α / 2)` and
`S α ^ (2 / α) ≤ D`. -/
theorem holder_lucas_of_one_lt_of_two_le (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} {p q u v α : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      (L n * L (n + 1) - 2 * k) / k ≤
        1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) ≤ (L n * L (n + 1) - 2 * k) / k := by
  have h := KTFib.holder_lucas_of_one_lt_of_two_le hk zero_le_one hL0 hL1
    (add_two_eq_mul_add_one_mul hL) (n := n) hpq hα h2α
  simp only [one_pow, one_mul, mul_one, sum_one, rpow_one_sub] at h
  exact h

/-- **Hölder-type chain, `p > 1`, `α < 2`** (Batte–Kaggwa, Theorem 1.2(ii)). Let `0 < k`,
`1 ≤ n`, let `p`, `q` be conjugate exponents and `α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and `D = (L n * L (n + 1) - 2 * k) / k`. Then
`S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` and `D ^ (α / 2) ≤ S α`. -/
theorem holder_lucas_of_one_lt_of_lt_two (hk : 0 < k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) {p q u v α : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (hα2 : α < 2) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, L i ^ α := by
  have h := KTFib.holder_lucas_of_one_lt_of_lt_two hk zero_le_one (.inr le_rfl) hL0 hL1
    (add_two_eq_mul_add_one_mul hL) hn hpq hα hα2
  simp only [one_pow, one_mul, mul_one] at h
  exact h

/-- **Hölder-type chain, `0 < p < 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(iii)). Let `0 < k`,
`0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `α = u / p + v / q ≥ 2`. Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ`
and `D = (L n * L (n + 1) - 2 * k) / k`. Then `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α` and
`S α ≤ D ^ (α / 2)`. -/
theorem holder_lucas_of_lt_one_of_two_le (hk : 0 < k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} {p q u v α : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤ ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) := by
  have h := KTFib.holder_lucas_of_lt_one_of_two_le hk zero_le_one (.inr le_rfl) hL0 hL1
    (add_two_eq_mul_add_one_mul hL) (n := n) hp0 hp1 hpq hα h2α
  simp only [one_pow, one_mul, mul_one] at h
  exact h

/-- **Hölder-type chain, `0 < p < 1`, `0 < α < 2`** (Batte–Kaggwa, Theorem 1.2(iv)). Let `1 ≤ k`,
`0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `0 < α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and `D = (L n * L (n + 1) - 2 * k) / k`. Then
`S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`, `S α ≤ 1 / n ^ (α / 2 - 1) * D ^ (α / 2)`,
`1 / n ^ (α / 2 - 1) * D ^ (α / 2) ≤ D` and `D ≤ S α ^ (2 / α)`. -/
theorem holder_lucas_of_lt_one_of_lt_two (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} {p q u v α : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α) (hα2 : α < 2) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤
        1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ≤
        (L n * L (n + 1) - 2 * k) / k ∧
      (L n * L (n + 1) - 2 * k) / k ≤ (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) := by
  have h := KTFib.holder_lucas_of_lt_one_of_lt_two hk zero_le_one hL0 hL1
    (add_two_eq_mul_add_one_mul hL) (n := n) hp0 hp1 hpq hα hα0 hα2
  simp only [one_pow, one_mul, mul_one, sum_one, rpow_one_sub] at h
  exact h

/-- **Converse Hölder inequalities, `p > 1`** (Batte–Kaggwa, Theorem 1.3). Let `1 ≤ k`,
`2 ≤ n`, let `p`, `q` be conjugate exponents with `u / p + v / q = 2` and `u ≠ v`, and let
`m`, `M` be the smaller and the larger of `L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)`
(hypotheses `hm`, `hM`); they bound every `L i ^ ((u - v) / p)`, `i ∈ Icc 1 n`
(`KTFib.lucas_rpow_mem_uIcc`). Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k) / k`. Then `0 < m < M` (`KTFib.min_lucas_rpow_pos`,
`KTFib.min_lucas_rpow_lt_max`),
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * D` and
`S u ^ (1 / p) * S v ^ (1 / q) ≤
(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D`. -/
theorem converse_holder_lucas_of_one_lt (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 2 ≤ n) {p q u v m M : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p))) :
    0 < m ∧ m < M ∧
      (M - m) * ∑ i ∈ Icc 1 n, L i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, L i ^ v ≤
        (M ^ p - m ^ p) * ((L n * L (n + 1) - 2 * k) / k) ∧
      (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          ((L n * L (n + 1) - 2 * k) / k) := by
  have h := KTFib.converse_holder_lucas_of_one_lt hk one_pos hL0 hL1
    (add_two_eq_mul_add_one_mul hL) hn hpq hα huv hm hM
  simp only [one_pow, one_mul, mul_one] at h
  exact h

/-- **Converse Hölder inequalities, `0 < p < 1`** (Batte–Kaggwa, Theorem 1.3). Let `1 ≤ k`,
`2 ≤ n`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1`, `u / p + v / q = 2` and `u ≠ v`, and let `m`, `M` be the
smaller and the larger of `L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)` (hypotheses `hm`,
`hM`); they bound every `L i ^ ((u - v) / p)`, `i ∈ Icc 1 n` (`KTFib.lucas_rpow_mem_uIcc`). Write
`S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and `D = (L n * L (n + 1) - 2 * k) / k`. Then `0 < m < M`
(`KTFib.min_lucas_rpow_pos`, `KTFib.min_lucas_rpow_lt_max`),
`(M ^ p - m ^ p) * D ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v` and
`(M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) * D ≤
S u ^ (1 / p) * S v ^ (1 / q)`. -/
theorem converse_holder_lucas_of_lt_one (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 2 ≤ n) {p q u v m M : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p))) :
    0 < m ∧ m < M ∧
      (M ^ p - m ^ p) * ((L n * L (n + 1) - 2 * k) / k) ≤
        (M - m) * ∑ i ∈ Icc 1 n, L i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, L i ^ v ∧
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          ((L n * L (n + 1) - 2 * k) / k) ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) := by
  have h := KTFib.converse_holder_lucas_of_lt_one hk one_pos hL0 hL1
    (add_two_eq_mul_add_one_mul hL) hn hp0 hp1 hpq hα huv hm hM
  simp only [one_pow, one_mul, mul_one] at h
  exact h

/-- **Converse Cauchy–Schwarz inequalities for `x i = L i * L (i + 1)`** (Batte–Kaggwa,
Theorem 1.4). Let `1 ≤ k`, `1 ≤ n` and `u + v = 2`, and write
`S γ = ∑ i ∈ Icc 1 n, x i ^ γ`. The hypotheses `hm₁`, ..., `hP` name the quantities involved:
`m₁`, `M₁` are the smaller and the larger of `x 1 ^ (u / 2)` and `x n ^ (u / 2)`, `m₂`, `M₂`
those of `x 1 ^ (v / 2)` and `x n ^ (v / 2)`, and `P = S 1` in closed form. Then
* `1 ≤ S u * S v / P ^ 2 ≤ (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4`;
* `S u / P - P / S v ≤ (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2`;
* `S u * S v - P ^ 2 ≤ n ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2`;
* `S v + m₂ * M₂ / (M₁ * m₁) * S u ≤ (M₂ / m₁ + m₂ / M₁) * P`. -/
theorem converse_cauchy_schwarz_lucas_mul_lucas_succ (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) {u v m₁ M₁ m₂ M₂ P : ℝ}
    (huv : u + v = 2)
    (hm₁ : m₁ = min ((L 1 * L 2) ^ (u / 2)) ((L n * L (n + 1)) ^ (u / 2)))
    (hM₁ : M₁ = max ((L 1 * L 2) ^ (u / 2)) ((L n * L (n + 1)) ^ (u / 2)))
    (hm₂ : m₂ = min ((L 1 * L 2) ^ (v / 2)) ((L n * L (n + 1)) ^ (v / 2)))
    (hM₂ : M₂ = max ((L 1 * L 2) ^ (v / 2)) ((L n * L (n + 1)) ^ (v / 2)))
    (hP : P = L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2)) :
    (1 ≤ (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u) * (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v) / P ^ 2 ∧
      (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u) * (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v) / P ^ 2 ≤
        (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4) ∧
    (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u) / P - P / (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v) ≤
      (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2 ∧
    (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u) * (∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v) - P ^ 2 ≤
      (n : ℝ) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 ∧
    ∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v +
        m₂ * M₂ / (M₁ * m₁) * ∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u ≤
      (M₂ / m₁ + m₂ / M₁) * P := by
  have hk0 : k ≠ 0 := (zero_lt_one.trans_le hk).ne'
  have h := KTFib.converse_cauchy_schwarz_lucas_mul_lucas_succ hk zero_le_one hL0 hL1
    (add_two_eq_mul_add_one_mul hL) hn huv hm₁ hM₁ hm₂ hM₂ (P := P) (by rw [hP]; field_simp; ring)
  simp only [one_pow, one_mul, sum_one] at h
  exact h

end KFib

