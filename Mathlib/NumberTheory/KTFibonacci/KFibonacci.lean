/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.KTFibonacci.CrossFamily
public import Mathlib.NumberTheory.KTFibonacci.Holder

/-!
# The `k`-Fibonacci and `k`-Lucas case: the results of Batte and Kaggwa

The `k`-Fibonacci numbers `F` and the `k`-Lucas numbers `L` of Falcón and Plaza satisfy
`F 0 = 0`, `F 1 = 1`, `L 0 = 2`, `L 1 = k` and `X (n + 2) = k * X (n + 1) + X n`; they are the
case `t = 1` of the `(k, t)`-sequences of `Mathlib.NumberTheory.KTFibonacci.Identities`. At
`t = 1` the weights `t ^ (n - i)` are all `1` and the total weight `∑ i ∈ Icc 1 n, 1` is `n`, so
the results of `Mathlib.NumberTheory.KTFibonacci.Holder` and
`Mathlib.NumberTheory.KTFibonacci.CrossFamily` become the unweighted results of Batte and Kaggwa.
This file states those whose shape changes at `t = 1`, each with the number of the corresponding
result of Batte and Kaggwa in its docstring. The other `(k, t)` lemmas apply verbatim at
`t = 1`, once the recurrence is written as `X (n + 2) = k * X (n + 1) + 1 * X n`: for instance
`KTFib.fib_mul_lucas` (`F i * L i = F (2 * i)`, Theorem 1.1), `KTFib.lucas_sq` (Lemma 2.2),
`KTFib.lucas_mul_succ` (Lemma 2.3) and `KTFib.lucas_lt_lucas_succ` (Lemma 2.4).

Batte and Kaggwa take `k` to be a positive integer. Here the identities hold over any field
with `k ≠ 0` (and `2 ≠ 0` for the sum of consecutive products), the cross-family bounds over any
linearly ordered field with `k ≠ 0`, and the Hölder-type inequalities for real `k` with `k > 0`
(Theorem 1.2(ii), (iii)) or `k ≥ 1` (Theorem 1.2(i), (iv), Theorems 1.3 and 1.4). Throughout,
`D = (L n * L (n + 1) - 2 * k) / k` is their `D_k(n)` and
`P = L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2)` is their `P_k(n)`.

At `k = 1` we also record their Corollary 5.1 for the Fibonacci numbers `Nat.fib` and the Lucas
numbers, over `ℤ`.

## References

* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
-/

public section

open Finset

namespace KFib

/-- The `k`-recurrence is the `(k, 1)`-recurrence. -/
private lemma rec_one {R : Type*} [Semiring R] {k : R} {G : ℕ → R}
    (hG : ∀ n, G (n + 2) = k * G (n + 1) + G n) (n : ℕ) :
    G (n + 2) = k * G (n + 1) + 1 * G n := by
  rw [hG n, one_mul]

/-! ### Closed forms (Theorem 1.1 and Theorem 4.1) -/

section Field

variable {K : Type*} [Field K] {k : K} {F L : ℕ → K}

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L i ^ 2 = (L n * L (n + 1) - 2 * k) / k`
(Batte–Kaggwa, Theorem 1.1). -/
theorem sum_sq_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i ^ 2 = (L n * L (n + 1) - 2 * k) / k := by
  simpa only [one_pow, one_mul, mul_one] using
    KTFib.sum_pow_mul_sq_lucas hk hL0 hL1 (rec_one hL) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F i ^ 2 = F n * F (n + 1) / k` (Batte–Kaggwa, Theorem 1.1). -/
theorem sum_sq_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, F i ^ 2 = F n * F (n + 1) / k := by
  simpa only [one_pow, one_mul] using KTFib.sum_pow_mul_sq_fib hk hF0 (rec_one hF) n

/-- For `k ≠ 0` and `2 ≠ 0`, `∑ i ∈ Icc 1 n, L i * L (i + 1) =
L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2)` (Batte–Kaggwa, Theorem 1.1). -/
theorem sum_lucas_mul_succ [NeZero (2 : K)] (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i * L (i + 1) =
      L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2) := by
  have h := KTFib.sum_pow_mul_lucas_mul_succ hk hL0 hL1 (rec_one hL) n
  simp only [one_pow, one_mul] at h
  rw [h]
  field_simp
  ring

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F i = (F n + F (n + 1) - 1) / k`
(Batte–Kaggwa, Theorem 4.1, (4.1)). -/
theorem sum_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i = (F n + F (n + 1) - 1) / k := by
  rw [KTFib.sum_fib (by simpa using hk) hF0 hF1 (rec_one hF)]
  ring

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L i = (L n + L (n + 1) - k - 2) / k`
(Batte–Kaggwa, Theorem 4.1, (4.2)). -/
theorem sum_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i = (L n + L (n + 1) - k - 2) / k := by
  rw [KTFib.sum_lucas (by simpa using hk) hL0 hL1 (rec_one hL)]
  ring

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F (2 * i - 1) = F (2 * n) / k`
(Batte–Kaggwa, Theorem 4.1, (4.3)). -/
theorem sum_fib_two_mul_sub_one (hk : k ≠ 0) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F (2 * i - 1) = F (2 * n) / k := by
  simpa only [one_pow, one_mul] using
    KTFib.sum_pow_mul_fib_two_mul_sub_one hk hF0 (rec_one hF) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F (2 * i) = (F (2 * n + 1) - 1) / k`
(Batte–Kaggwa, Theorem 4.1, (4.4)). -/
theorem sum_fib_two_mul (hk : k ≠ 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, F (2 * i) = (F (2 * n + 1) - 1) / k := by
  simpa only [one_pow, one_mul] using KTFib.sum_pow_mul_fib_two_mul hk hF1 (rec_one hF) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L (2 * i - 1) = (L (2 * n) - 2) / k`
(Batte–Kaggwa, Theorem 4.1, (4.5)). -/
theorem sum_lucas_two_mul_sub_one (hk : k ≠ 0) (hL0 : L 0 = 2)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L (2 * i - 1) = (L (2 * n) - 2) / k := by
  simpa only [one_pow, one_mul, mul_one] using
    KTFib.sum_pow_mul_lucas_two_mul_sub_one hk hL0 (rec_one hL) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L (2 * i) = (L (2 * n + 1) - k) / k`
(Batte–Kaggwa, Theorem 4.1, (4.6)). -/
theorem sum_lucas_two_mul (hk : k ≠ 0) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L (2 * i) = (L (2 * n + 1) - k) / k := by
  simpa only [one_pow, one_mul, mul_one] using
    KTFib.sum_pow_mul_lucas_two_mul hk hL1 (rec_one hL) n

end Field

/-! ### The cross-family bound (Theorem 1.5 and Corollary 4.1) -/

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {k : K} {F L : ℕ → K}

/-- For `k ≠ 0`,
`(∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k)`
(Batte–Kaggwa, Theorem 1.5). -/
theorem sq_sum_fib_two_mul_le (hk : k ≠ 0) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  simpa only [one_pow, one_mul, mul_one] using KTFib.sq_sum_pow_mul_fib_two_mul_le hk
    zero_le_one hF0 (rec_one hF) hL0 hL1 (rec_one hL) n

/-- For `k ≠ 0` and `n ≥ 1`,
`(∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 = F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k)` if and
only if `n = 1` (Batte–Kaggwa, Theorem 1.5). -/
theorem sq_sum_fib_two_mul_eq_iff (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 = F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) ↔
      n = 1 := by
  simpa only [one_pow, one_mul, mul_one] using KTFib.sq_sum_pow_mul_fib_two_mul_eq_iff hk
    one_pos hF0 hF1 (rec_one hF) hL0 hL1 (rec_one hL) hn

/-- For `k ≠ 0`,
`((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k)`
(Batte–Kaggwa, Corollary 4.1). -/
theorem sq_fib_sub_one_div_le (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  rw [← sum_fib_two_mul hk hF1 hF]
  exact sq_sum_fib_two_mul_le hk hF0 hF hL0 hL1 hL n

end LinearOrderedField

/-! ### Hölder-type inequalities (Theorems 1.2, 1.3 and 1.4) -/

section Real

variable {k : ℝ} {L : ℕ → ℝ}

/-- At `t = 1` the total weight is `n`. -/
private lemma sum_one (n : ℕ) : ∑ _i ∈ Icc 1 n, (1 : ℝ) = n := by
  simp

/-- `n ^ (1 - α / 2) = 1 / n ^ (α / 2 - 1)`, the form used by Batte and Kaggwa. -/
private lemma rpow_one_sub (n : ℕ) (α : ℝ) :
    (n : ℝ) ^ (1 - α / 2) = 1 / (n : ℝ) ^ (α / 2 - 1) := by
  rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n), neg_sub]

/-- **Hölder sandwich, `p > 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(i)). Let `1 ≤ k`, let `p`,
`q` be conjugate exponents and `α = u / p + v / q ≥ 2`. Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k) / k`. Then `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`,
`1 / n ^ (α / 2 - 1) * D ^ (α / 2) ≤ S α`, `D ≤ 1 / n ^ (α / 2 - 1) * D ^ (α / 2)` and
`S α ^ (2 / α) ≤ D`. -/
theorem holder_sandwich_of_one_lt_of_two_le (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} {p q u v α : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      (L n * L (n + 1) - 2 * k) / k ≤
        1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) ≤ (L n * L (n + 1) - 2 * k) / k := by
  have h := KTFib.holder_sandwich_of_one_lt_of_two_le hk le_rfl hL0 hL1 (rec_one hL) (n := n)
    hpq hα h2α
  simp only [one_pow, one_mul, mul_one, sum_one, rpow_one_sub] at h
  exact h

/-- **Hölder sandwich, `p > 1`, `0 ≤ α < 2`** (Batte–Kaggwa, Theorem 1.2(ii)). Let `0 < k`,
`1 ≤ n`, let `p`, `q` be conjugate exponents and `0 ≤ α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and `D = (L n * L (n + 1) - 2 * k) / k`. Then
`S α ≤ S u ^ (1 / p) * S v ^ (1 / q)` and `D ^ (α / 2) ≤ S α`. -/
theorem holder_sandwich_of_one_lt_of_lt_two (hk : 0 < k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) {p q u v α : ℝ}
    (hpq : p.HolderConjugate q) (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hα2 : α < 2) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, L i ^ α := by
  have h := KTFib.holder_sandwich_of_one_lt_of_lt_two hk le_rfl hL0 hL1 (rec_one hL) hn hpq hα
    hα0 hα2
  simp only [one_pow, one_mul, mul_one] at h
  exact h

/-- **Hölder sandwich, `0 < p < 1`, `α ≥ 2`** (Batte–Kaggwa, Theorem 1.2(iii)). Let `0 < k`,
`0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `α = u / p + v / q ≥ 2`. Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ`
and `D = (L n * L (n + 1) - 2 * k) / k`. Then `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α` and
`S α ≤ D ^ (α / 2)`. -/
theorem holder_sandwich_of_lt_one_of_two_le (hk : 0 < k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} {p q u v α : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤ ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) := by
  have h := KTFib.holder_sandwich_of_lt_one_of_two_le hk le_rfl hL0 hL1 (rec_one hL) (n := n)
    hp0 hp1 hpq hα h2α
  simp only [one_pow, one_mul, mul_one] at h
  exact h

/-- **Hölder sandwich, `0 < p < 1`, `0 < α < 2`** (Batte–Kaggwa, Theorem 1.2(iv)). Let `1 ≤ k`,
`0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `0 < α = u / p + v / q < 2`. Write
`S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and `D = (L n * L (n + 1) - 2 * k) / k`. Then
`S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`, `S α ≤ 1 / n ^ (α / 2 - 1) * D ^ (α / 2)`,
`1 / n ^ (α / 2 - 1) * D ^ (α / 2) ≤ D` and `D ≤ S α ^ (2 / α)`. -/
theorem holder_sandwich_of_lt_one_of_lt_two (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} {p q u v α : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α) (hα2 : α < 2) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤
        1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * ((L n * L (n + 1) - 2 * k) / k) ^ (α / 2) ≤
        (L n * L (n + 1) - 2 * k) / k ∧
      (L n * L (n + 1) - 2 * k) / k ≤ (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) := by
  have h := KTFib.holder_sandwich_of_lt_one_of_lt_two hk le_rfl hL0 hL1 (rec_one hL) (n := n)
    hp0 hp1 hpq hα hα0 hα2
  simp only [one_pow, one_mul, mul_one, sum_one, rpow_one_sub] at h
  exact h

/-- **Converse Hölder inequalities, `p > 1`** (Batte–Kaggwa, Theorem 1.3). Let `1 ≤ k`,
`2 ≤ n`, let `p`, `q` be conjugate exponents with `u / p + v / q = 2` and `u ≠ v`, and let
`m`, `M` be the smaller and the larger of `L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)`
(hypotheses `hm`, `hM`). Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and
`D = (L n * L (n + 1) - 2 * k) / k`. Then `0 < m < M`,
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
  subst hm hM
  obtain ⟨hm0, hmM, hr⟩ := KTFib.lucas_rpow_bounds hk one_pos hL0 hL1 (rec_one hL) hn
    (div_ne_zero (sub_ne_zero.2 huv) hpq.ne_zero)
  have h := KTFib.converse_holder_lucas_of_one_lt (zero_lt_one.trans_le hk) zero_le_one hL0 hL1
    (rec_one hL) hpq hα hm0 hmM hr
  simp only [one_pow, one_mul, mul_one] at h
  exact ⟨hm0, hmM, h⟩

/-- **Converse Hölder inequalities, `0 < p < 1`** (Batte–Kaggwa, Theorem 1.3). Let `1 ≤ k`,
`2 ≤ n`, `0 < p < 1`, `p⁻¹ + q⁻¹ = 1`, `u / p + v / q = 2` and `u ≠ v`, and let `m`, `M` be the
smaller and the larger of `L 1 ^ ((u - v) / p)` and `L n ^ ((u - v) / p)` (hypotheses `hm`,
`hM`). Write `S γ = ∑ i ∈ Icc 1 n, L i ^ γ` and `D = (L n * L (n + 1) - 2 * k) / k`. Then
`0 < m < M`, `(M ^ p - m ^ p) * D ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v` and
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
  subst hm hM
  obtain ⟨hm0, hmM, hr⟩ := KTFib.lucas_rpow_bounds hk one_pos hL0 hL1 (rec_one hL) hn
    (div_ne_zero (sub_ne_zero.2 huv) hp0.ne')
  have h := KTFib.converse_holder_lucas_of_lt_one (zero_lt_one.trans_le hk) zero_le_one hL0 hL1
    (rec_one hL) hp0 hp1 hpq hα hm0 hmM hr
  simp only [one_pow, one_mul, mul_one] at h
  exact ⟨hm0, hmM, h⟩

/-- **Converse Cauchy–Schwarz inequalities for `x i = L i * L (i + 1)`** (Batte–Kaggwa,
Theorem 1.4). Let `1 ≤ k`, `1 ≤ n` and `u + v = 2`, and write
`S γ = ∑ i ∈ Icc 1 n, x i ^ γ`. The hypotheses `hm₁`, ..., `hP` name the quantities involved:
`m₁`, `M₁` are the smaller and the larger of `x 1 ^ (u / 2)` and `x n ^ (u / 2)`, `m₂`, `M₂`
those of `x 1 ^ (v / 2)` and `x n ^ (v / 2)`, and `P = S 1` in closed form. Then
* `1 ≤ S u * S v / P ^ 2 ≤ (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4`;
* `S u / P - P / S v ≤ (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2`;
* `S u * S v - P ^ 2 ≤ n ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2`;
* `S v + m₂ * M₂ / (M₁ * m₁) * S u ≤ (M₂ / m₁ + m₂ / M₁) * P`. -/
theorem converse_cauchy_lucas (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
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
  have h := KTFib.converse_cauchy_lucas hk zero_le_one hL0 hL1 (rec_one hL) hn huv hm₁ hM₁ hm₂
    hM₂ (P := P) (by rw [hP]; field_simp; ring)
  simp only [one_pow, one_mul, sum_one] at h
  exact h

end Real

end KFib

/-! ### `k = 1`: the Fibonacci and Lucas numbers (Corollary 5.1) -/

/-- For the Fibonacci numbers `Nat.fib` and the Lucas numbers `L`,
`(fib (2 * n + 1) - 1) ^ 2 ≤ fib n * fib (n + 1) * (L n * L (n + 1) - 2)` in `ℤ`
(Batte–Kaggwa, Corollary 5.1). -/
theorem Nat.sq_fib_two_mul_add_one_sub_one_le {L : ℕ → ℤ} (hL0 : L 0 = 2) (hL1 : L 1 = 1)
    (hL : ∀ n, L (n + 2) = L (n + 1) + L n) (n : ℕ) :
    ((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 ≤
      Nat.fib n * Nat.fib (n + 1) * (L n * L (n + 1) - 2) := by
  have h := KTFib.sq_fib_sub_le (F := fun n ↦ (Nat.fib n : ℤ)) (k := 1) zero_le_one (by simp)
    (by simp) (fun n ↦ by push_cast [Nat.fib_add_two]; ring) hL0 hL1
    (fun n ↦ by rw [hL]; ring) n
  simpa only [one_pow, mul_one] using h

/-- For the Fibonacci numbers `Nat.fib`, the Lucas numbers `L` and `n ≥ 1`,
`(fib (2 * n + 1) - 1) ^ 2 = fib n * fib (n + 1) * (L n * L (n + 1) - 2)` in `ℤ` if and only if
`n = 1` (Batte–Kaggwa, Corollary 5.1). -/
theorem Nat.sq_fib_two_mul_add_one_sub_one_eq_iff {L : ℕ → ℤ} (hL0 : L 0 = 2) (hL1 : L 1 = 1)
    (hL : ∀ n, L (n + 2) = L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 =
        Nat.fib n * Nat.fib (n + 1) * (L n * L (n + 1) - 2) ↔ n = 1 := by
  have h := KTFib.sq_fib_sub_eq_iff (F := fun n ↦ (Nat.fib n : ℤ)) (k := 1) one_ne_zero one_pos
    (by simp) (by simp) (fun n ↦ by push_cast [Nat.fib_add_two]; ring) hL0 hL1
    (fun n ↦ by rw [hL]; ring) hn
  simpa only [one_pow, mul_one] using h
