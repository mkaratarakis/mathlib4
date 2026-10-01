/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.KTFibonacci.CrossFamily
import Mathlib.Tactic.FieldSimp

/-!
# The `k`-Fibonacci and `k`-Lucas case: the identities of Batte and Kaggwa

The `k`-Fibonacci numbers `F` of Falcón and Plaza and the `k`-Lucas numbers `L` of Falcón satisfy
`F 0 = 0`, `F 1 = 1`, `L 0 = 2`, `L 1 = k` and `X (n + 2) = k * X (n + 1) + X n`; they are the
case `t = 1` of the `(k, t)`-sequences of `Mathlib.NumberTheory.KTFibonacci.Identities`. At
`t = 1` the weights `t ^ (n - i)` are all `1`, so the closed forms of
`Mathlib.NumberTheory.KTFibonacci.Identities` and the cross-family bound of
`Mathlib.NumberTheory.KTFibonacci.CrossFamily` become the unweighted results of Batte and Kaggwa.
This file states those whose shape changes at `t = 1`, each with the number of the corresponding
result of Batte and Kaggwa in its docstring. The other `(k, t)` lemmas apply verbatim at `t = 1`,
once the recurrence is written as `X (n + 2) = k * X (n + 1) + 1 * X n`
(`KFib.add_two_eq_mul_add_one_mul`): for instance `KTFib.fib_mul_lucas`
(`F i * L i = F (2 * i)`, Theorem 1.1), `KTFib.lucas_sq` (Lemma 2.2), `KTFib.lucas_mul_lucas_succ`
(Lemma 2.3) and `KTFib.lucas_lt_lucas_succ` (Lemma 2.4). The Hölder-type inequalities at
`t = 1` (Theorems 1.2, 1.3 and 1.4) are at the end of `Mathlib.NumberTheory.KTFibonacci.Holder`.

Batte and Kaggwa take `k` to be a positive integer. Here the identities hold over any field,
with `k ≠ 0` except for the sum of the terms of even index (and `2 ≠ 0` for the sum of
consecutive products), and the cross-family bounds hold over any linearly ordered field.

At `k = 1` we also record their Corollary 5.1 for the Fibonacci numbers `Nat.fib` and the Lucas
numbers, over `ℤ`.

## References

* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
* [S. Falcón and Á. Plaza, *The `k`-Fibonacci sequence and the Pascal
  2-triangle*][falcon_plaza_2007]
* [S. Falcón, *On the `k`-Lucas numbers*][falcon_2011]
-/

public section

open Finset

namespace KFib

/-! ### Closed forms (Theorem 1.1 and Theorem 4.1) -/

section Field

variable {K : Type*} [Field K] {k : K} {F L : ℕ → K}

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L i ^ 2 = (L n * L (n + 1) - 2 * k) / k`
(Batte–Kaggwa, Theorem 1.1). -/
theorem sum_lucas_sq (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i ^ 2 = (L n * L (n + 1) - 2 * k) / k := by
  simpa only [one_pow, one_mul, mul_one] using
    KTFib.sum_pow_mul_lucas_sq hk hL0 hL1 (add_two_eq_mul_add_one_mul hL) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F i ^ 2 = F n * F (n + 1) / k` (Batte–Kaggwa, Theorem 1.1). -/
theorem sum_fib_sq (hk : k ≠ 0) (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
    (n : ℕ) : ∑ i ∈ Icc 1 n, F i ^ 2 = F n * F (n + 1) / k := by
  simpa only [one_pow, one_mul] using
    KTFib.sum_pow_mul_fib_sq hk hF0 (add_two_eq_mul_add_one_mul hF) n

/-- For `k ≠ 0` and `2 ≠ 0`, `∑ i ∈ Icc 1 n, L i * L (i + 1) =
L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2)` (Batte–Kaggwa, Theorem 1.1). -/
theorem sum_lucas_mul_lucas_succ [NeZero (2 : K)] (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i * L (i + 1) =
      L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2) := by
  have h := KTFib.sum_pow_mul_lucas_mul_lucas_succ hk hL0 hL1 (add_two_eq_mul_add_one_mul hL) n
  simp only [one_pow, one_mul] at h
  rw [h]
  field_simp
  ring

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F i = (F n + F (n + 1) - 1) / k`
(Batte–Kaggwa, Theorem 4.1, (4.1)). -/
theorem sum_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i = (F n + F (n + 1) - 1) / k := by
  rw [KTFib.sum_fib (by simpa using hk) hF0 hF1 (add_two_eq_mul_add_one_mul hF)]
  ring

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L i = (L n + L (n + 1) - k - 2) / k`
(Batte–Kaggwa, Theorem 4.1, (4.2)). -/
theorem sum_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i = (L n + L (n + 1) - k - 2) / k := by
  rw [KTFib.sum_lucas (by simpa using hk) hL0 hL1 (add_two_eq_mul_add_one_mul hL)]
  ring

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, F (2 * i - 1) = F (2 * n) / k`
(Batte–Kaggwa, Theorem 4.1, (4.3)). -/
theorem sum_fib_two_mul_sub_one (hk : k ≠ 0) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F (2 * i - 1) = F (2 * n) / k := by
  simpa only [one_pow, one_mul] using
    KTFib.sum_pow_mul_fib_two_mul_sub_one hk hF0 (add_two_eq_mul_add_one_mul hF) n

/-- `∑ i ∈ Icc 1 n, F (2 * i) = (F (2 * n + 1) - 1) / k` (Batte–Kaggwa, Theorem 4.1, (4.4)). -/
theorem sum_fib_two_mul (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F (2 * i) = (F (2 * n + 1) - 1) / k := by
  simpa only [one_pow, one_mul] using
    KTFib.sum_pow_mul_fib_two_mul hF0 hF1 (add_two_eq_mul_add_one_mul hF) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L (2 * i - 1) = (L (2 * n) - 2) / k`
(Batte–Kaggwa, Theorem 4.1, (4.5)). -/
theorem sum_lucas_two_mul_sub_one (hk : k ≠ 0) (hL0 : L 0 = 2)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L (2 * i - 1) = (L (2 * n) - 2) / k := by
  simpa only [one_pow, one_mul, mul_one] using
    KTFib.sum_pow_mul_lucas_two_mul_sub_one hk hL0 (add_two_eq_mul_add_one_mul hL) n

/-- For `k ≠ 0`, `∑ i ∈ Icc 1 n, L (2 * i) = (L (2 * n + 1) - k) / k`
(Batte–Kaggwa, Theorem 4.1, (4.6)). -/
theorem sum_lucas_two_mul (hk : k ≠ 0) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L (2 * i) = (L (2 * n + 1) - k) / k := by
  simpa only [one_pow, one_mul, mul_one] using
    KTFib.sum_pow_mul_lucas_two_mul hk hL1 (add_two_eq_mul_add_one_mul hL) n

end Field

/-! ### The cross-family bound (Theorem 1.5 and Corollary 4.1) -/

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {k : K} {F L : ℕ → K}

/-- `(∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k)`
(Batte–Kaggwa, Theorem 1.5). -/
theorem sq_sum_fib_two_mul_le (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  simpa only [one_pow, one_mul, mul_one] using KTFib.sq_sum_pow_mul_fib_two_mul_le
    zero_le_one hF0 (add_two_eq_mul_add_one_mul hF) hL0 hL1 (add_two_eq_mul_add_one_mul hL) n

/-- For `k ≠ 0` and `n ≥ 1`,
`(∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 = F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k)` if and
only if `n = 1` (Batte–Kaggwa, Theorem 1.5). -/
theorem sq_sum_fib_two_mul_eq_iff (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 = F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) ↔
      n = 1 := by
  simpa only [one_pow, one_mul, mul_one] using KTFib.sq_sum_pow_mul_fib_two_mul_eq_iff hk
    one_pos hF0 hF1 (add_two_eq_mul_add_one_mul hF) hL0 hL1 (add_two_eq_mul_add_one_mul hL) hn

/-- `((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k)`
(Batte–Kaggwa, Corollary 4.1). -/
theorem sq_fib_two_mul_add_one_sub_one_div_le (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  rw [← sum_fib_two_mul hF0 hF1 hF]
  exact sq_sum_fib_two_mul_le hF0 hF hL0 hL1 hL n

end LinearOrderedField

end KFib

/-! ### `k = 1`: the Fibonacci and Lucas numbers (Corollary 5.1) -/

/-- For the Fibonacci numbers `Nat.fib` and the Lucas numbers `L`,
`(fib (2 * n + 1) - 1) ^ 2 ≤ fib n * fib (n + 1) * (L n * L (n + 1) - 2)` in `ℤ`
(Batte–Kaggwa, Corollary 5.1). -/
theorem Nat.sq_fib_two_mul_add_one_sub_one_le {L : ℕ → ℤ} (hL0 : L 0 = 2) (hL1 : L 1 = 1)
    (hL : ∀ n, L (n + 2) = L (n + 1) + L n) (n : ℕ) :
    ((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 ≤
      Nat.fib n * Nat.fib (n + 1) * (L n * L (n + 1) - 2) := by
  have h := KTFib.sq_fib_two_mul_add_one_sub_pow_le (F := fun n ↦ (Nat.fib n : ℤ)) (k := 1)
    zero_le_one (by simp) (by simp) (fun n ↦ by push_cast [Nat.fib_add_two]; ring) hL0 hL1
    (fun n ↦ by rw [hL]; ring) n
  simpa only [one_pow, mul_one] using h

/-- For the Fibonacci numbers `Nat.fib`, the Lucas numbers `L` and `n ≥ 1`,
`(fib (2 * n + 1) - 1) ^ 2 = fib n * fib (n + 1) * (L n * L (n + 1) - 2)` in `ℤ` if and only if
`n = 1` (Batte–Kaggwa, Corollary 5.1). -/
theorem Nat.sq_fib_two_mul_add_one_sub_one_eq_iff {L : ℕ → ℤ} (hL0 : L 0 = 2) (hL1 : L 1 = 1)
    (hL : ∀ n, L (n + 2) = L (n + 1) + L n) {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 =
        Nat.fib n * Nat.fib (n + 1) * (L n * L (n + 1) - 2) ↔ n = 1 := by
  have h := KTFib.sq_fib_two_mul_add_one_sub_pow_eq_iff (F := fun n ↦ (Nat.fib n : ℤ)) (k := 1)
    one_ne_zero one_pos (by simp) (by simp) (fun n ↦ by push_cast [Nat.fib_add_two]; ring) hL0 hL1
    (fun n ↦ by rw [hL]; ring) hn
  simpa only [one_pow, mul_one] using h
