/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.KTFibonacci.Identities

/-!
# Rescaling `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences to `t = 1`

Let `F` and `L` be the `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences over a field, and let
`s ≠ 0` with `s ^ 2 = t` (over the reals, `s = √t` for `t > 0`). Then `g i = L i / s ^ i` and
`f i = s * F i / s ^ i` are the `k'`-Lucas and `k'`-Fibonacci numbers for `k' = k / s`, i.e. the
`(k', 1)`-sequences. For `1 ≤ i ≤ n` the terms of the weighted sums with weight `t ^ (n - i)` are
multiples of the corresponding terms for `g` and `f` by factors that do not depend on `i`:
`t ^ (n - i) * L i ^ 2 = t ^ n * g i ^ 2`, `t * (t ^ (n - i) * F i ^ 2) = t ^ n * f i ^ 2`, and so
on. Consequently each weighted closed form of `Mathlib.NumberTheory.KTFibonacci.Identities` (the
sums of `L i ^ 2`, `F i ^ 2`, `L i * L (i + 1)`, `F (2 * i - 1)`, `F (2 * i)`, `L (2 * i - 1)` and
`L (2 * i)`) and the cross-family bound of `Mathlib.NumberTheory.KTFibonacci.CrossFamily`, with its
equality case, is equivalent to the corresponding statement of Batte and Kaggwa for `f`, `g` and
the parameter `k'` (see `Mathlib.NumberTheory.KTFibonacci.KFibonacci`).

For exponents other than `2` there is no such reduction: the ratio of `t ^ (n - i) * x ^ α` to
`(x / √t ^ i) ^ α` is `t ^ (n + (α / 2 - 1) * i)`, which depends on `i` unless `α = 2` or `t = 1`.

## Main results

* `KTFib.rescale_lucas`, `KTFib.rescale_fib`: `g` and `f` are the `(k / s, 1)`-Lucas and
  `(k / s, 1)`-Fibonacci sequences.
* `KTFib.rescale_sum_lucas`, `KTFib.rescale_sum_fib`: the weighted sums for `L` and `F` are fixed
  multiples of the unweighted sums for `g` and `f`.
* `KTFib.rescale_sum_lucas_sq_iff`, ..., `KTFib.rescale_sum_lucas_two_mul_iff`: each weighted
  closed form for `(k, t)` is equivalent to the unweighted closed form for `(k / s, 1)`.
* `KTFib.rescale_sq_sum_fib_two_mul_le_iff`, `KTFib.rescale_sq_sum_fib_two_mul_eq_iff`,
  `KTFib.rescale_sq_fib_two_mul_add_one_sub_pow_le_iff`,
  `KTFib.rescale_sq_fib_two_mul_add_one_sub_pow_eq_iff`: the same for the two forms of the
  cross-family bound and their equality cases, over a linearly ordered field.
* `KTFib.rescale_sq_jacobsthal_two_mul_add_one_sub_pow_iff`: the case of the Jacobsthal numbers,
  `(k, t) = (1, 2)`, `k' = 1 / √2`.
* `KTFib.div_sqrt_lt_one`: `k' = k / √t < 1` when `0 ≤ k` and `k ^ 2 < t`.
* `KTFib.pow_sub_mul_rpow_eq`: the ratio `t ^ (n + (α / 2 - 1) * i)` for real exponents `α`.

## References

* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
-/

public section

open Finset

namespace KTFib

/-! ### Rescaling over a field -/

section Field

variable {K : Type*} [Field K] {k t s : K} {G F L f g : ℕ → K}

/-- If `G` solves `G (n + 2) = k * G (n + 1) + t * G n` and `s ≠ 0` with `s ^ 2 = t`, then
`i ↦ G i / s ^ i` solves the `(k / s, 1)`-recurrence:
`G (n + 2) / s ^ (n + 2) = k / s * (G (n + 1) / s ^ (n + 1)) + G n / s ^ n`. -/
theorem div_pow_add_two (hs : s ≠ 0) (hst : s ^ 2 = t)
    (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    G (n + 2) / s ^ (n + 2) = k / s * (G (n + 1) / s ^ (n + 1)) + G n / s ^ n := by
  subst hst
  rw [hG]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, the rescaled `(k, t)`-Lucas numbers `g i = L i / s ^ i` are the
`k / s`-Lucas numbers: `g 0 = 2`, `g 1 = k / s` and `g (n + 2) = k / s * g (n + 1) + g n`. -/
theorem rescale_lucas (hs : s ≠ 0) (hst : s ^ 2 = t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (hg : ∀ i, g i = L i / s ^ i) :
    g 0 = 2 ∧ g 1 = k / s ∧ ∀ n, g (n + 2) = k / s * g (n + 1) + g n := by
  simp only [hg]
  exact ⟨by simp [hL0], by simp [hL1], div_pow_add_two hs hst hL⟩

/-- For `s ≠ 0` with `s ^ 2 = t`, the rescaled `(k, t)`-Fibonacci numbers `f i = s * F i / s ^ i`
are the `k / s`-Fibonacci numbers: `f 0 = 0`, `f 1 = 1` and `f (n + 2) = k / s * f (n + 1) + f n`.
-/
theorem rescale_fib (hs : s ≠ 0) (hst : s ^ 2 = t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hf : ∀ i, f i = s * F i / s ^ i) :
    f 0 = 0 ∧ f 1 = 1 ∧ ∀ n, f (n + 2) = k / s * f (n + 1) + f n := by
  simp only [hf, mul_div_assoc]
  refine ⟨by simp [hF0], by simp [hF1, hs], fun n ↦ ?_⟩
  rw [div_pow_add_two hs hst hF]
  ring

/-- `t ^ (n - i) * (s ^ (2 * i) * x) = t ^ n * x` for `i ≤ n` and `s ^ 2 = t`. -/
private lemma pow_sub_mul_pow_two_mul (hst : s ^ 2 = t) {i n : ℕ} (hi : i ≤ n) (x : K) :
    t ^ (n - i) * (s ^ (2 * i) * x) = t ^ n * x := by
  rw [← hst, ← mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
  congr 2
  omega

/-- For `s ≠ 0` with `s ^ 2 = t` and `g i = L i / s ^ i` (for any sequence `L`), the weighted sums
of `L i ^ 2`, `L i * L (i + 1)`, `L (2 * i)` and `L (2 * i - 1)` are fixed multiples of the
unweighted sums for `g`:
`∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = t ^ n * ∑ i ∈ Icc 1 n, g i ^ 2`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) = t ^ n * s * ∑ i ∈ Icc 1 n, g i * g (i + 1)`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = t ^ n * ∑ i ∈ Icc 1 n, g (2 * i)` and
`s * ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = t ^ n * ∑ i ∈ Icc 1 n, g (2 * i - 1)`. -/
theorem rescale_sum_lucas (hs : s ≠ 0) (hst : s ^ 2 = t) (hg : ∀ i, g i = L i / s ^ i)
    (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = t ^ n * ∑ i ∈ Icc 1 n, g i ^ 2 ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
        t ^ n * s * ∑ i ∈ Icc 1 n, g i * g (i + 1) ∧
      ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = t ^ n * ∑ i ∈ Icc 1 n, g (2 * i) ∧
      s * ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) =
        t ^ n * ∑ i ∈ Icc 1 n, g (2 * i - 1) := by
  have hL (i : ℕ) : L i = s ^ i * g i := by rw [hg, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
  simp only [mul_sum]
  refine ⟨sum_congr rfl fun i hi ↦ ?_, sum_congr rfl fun i hi ↦ ?_,
    sum_congr rfl fun i hi ↦ ?_, sum_congr rfl fun i hi ↦ ?_⟩ <;>
    obtain ⟨hi1, hin⟩ := mem_Icc.1 hi
  · rw [← pow_sub_mul_pow_two_mul hst hin, hL]
    ring
  · rw [mul_assoc (t ^ n), ← pow_sub_mul_pow_two_mul hst hin, hL, hL]
    ring
  · rw [← pow_sub_mul_pow_two_mul hst hin, hL]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    rw [← pow_sub_mul_pow_two_mul hst hin, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, hL]
    ring

/-- For `s ≠ 0` with `s ^ 2 = t` and `f i = s * F i / s ^ i` (for any sequence `F`), the weighted
sums of `F i ^ 2`, `F (2 * i)` and `F (2 * i - 1)` are fixed multiples of the unweighted sums for
`f`: `t * ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = t ^ n * ∑ i ∈ Icc 1 n, f i ^ 2`,
`s * ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = t ^ n * ∑ i ∈ Icc 1 n, f (2 * i)` and
`t * ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = t ^ n * ∑ i ∈ Icc 1 n, f (2 * i - 1)`. -/
theorem rescale_sum_fib (hs : s ≠ 0) (hst : s ^ 2 = t) (hf : ∀ i, f i = s * F i / s ^ i)
    (n : ℕ) :
    t * ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = t ^ n * ∑ i ∈ Icc 1 n, f i ^ 2 ∧
      s * ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = t ^ n * ∑ i ∈ Icc 1 n, f (2 * i) ∧
      t * ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) =
        t ^ n * ∑ i ∈ Icc 1 n, f (2 * i - 1) := by
  have hF (i : ℕ) : s * F i = s ^ i * f i := by rw [hf, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
  simp only [mul_sum]
  refine ⟨sum_congr rfl fun i hi ↦ ?_, sum_congr rfl fun i hi ↦ ?_,
    sum_congr rfl fun i hi ↦ ?_⟩ <;>
    obtain ⟨hi1, hin⟩ := mem_Icc.1 hi
  · rw [← pow_sub_mul_pow_two_mul hst hin, ← hst]
    linear_combination s ^ (2 * (n - i)) * (s * F i + s ^ i * f i) * hF i
  · rw [← pow_sub_mul_pow_two_mul hst hin]
    linear_combination t ^ (n - i) * hF (2 * i)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    rw [← pow_sub_mul_pow_two_mul hst hin, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, ← hst]
    linear_combination s ^ (2 * (n - (j + 1))) * s * hF (2 * j + 1)


/-- If `c * X' = d * X` and `c * Y' = d * Y` with `c, d ≠ 0`, then `X = Y ↔ X' = Y'`. -/
private lemma eq_iff_eq_of_mul_eq {c d X Y X' Y' : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (hX : c * X' = d * X) (hY : c * Y' = d * Y) : X = Y ↔ X' = Y' := by
  rw [← mul_right_inj' hd, ← hX, ← hY, mul_right_inj' hc]

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0` and `g i = L i / s ^ i`, the weighted closed form
`∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = (L n * L (n + 1) - 2 * k * t ^ n) / k` is equivalent to the
unweighted closed form `∑ i ∈ Icc 1 n, g i ^ 2 = (g n * g (n + 1) - 2 * k') / k'` for
`k' = k / s` (Batte–Kaggwa, Theorem 1.1). -/
theorem rescale_sum_lucas_sq_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = (L n * L (n + 1) - 2 * k * t ^ n) / k ↔
      ∑ i ∈ Icc 1 n, g i ^ 2 = (g n * g (n + 1) - 2 * (k / s)) / (k / s) := by
  refine eq_iff_eq_of_mul_eq (pow_ne_zero n (hst ▸ pow_ne_zero 2 hs)) one_ne_zero
    (by rw [one_mul, (rescale_sum_lucas hs hst hg n).1]) ?_
  rw [hg, hg, ← hst]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0` and `f i = s * F i / s ^ i`, the weighted closed form
`∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k` is equivalent to the unweighted closed
form `∑ i ∈ Icc 1 n, f i ^ 2 = f n * f (n + 1) / k'` for `k' = k / s` (Batte–Kaggwa, Theorem 1.1).
-/
theorem rescale_sum_fib_sq_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hf : ∀ i, f i = s * F i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k ↔
      ∑ i ∈ Icc 1 n, f i ^ 2 = f n * f (n + 1) / (k / s) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (pow_ne_zero n ht) ht (rescale_sum_fib hs hst hf n).1.symm ?_
  rw [hf, hf, ← hst]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0`, `2 ≠ 0` and `g i = L i / s ^ i`, the weighted closed
form `∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
(L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k` is equivalent to
the unweighted closed form `∑ i ∈ Icc 1 n, g i * g (i + 1) =
g (n + 1) ^ 2 / k' - k' + ((-1) ^ n - 1) * (2 / k' + k' / 2)` for `k' = k / s`
(Batte–Kaggwa, Theorem 1.1). -/
theorem rescale_sum_lucas_mul_lucas_succ_iff [NeZero (2 : K)] (hs : s ≠ 0) (hst : s ^ 2 = t)
    (hk : k ≠ 0) (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
        (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k ↔
      ∑ i ∈ Icc 1 n, g i * g (i + 1) =
        g (n + 1) ^ 2 / (k / s) - k / s + ((-1) ^ n - 1) * (2 / (k / s) + k / s / 2) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (mul_ne_zero (pow_ne_zero n ht) hs) one_ne_zero
    (by rw [one_mul, (rescale_sum_lucas hs hst hg n).2.1]) ?_
  rw [hg, ← hst]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0` and `f i = s * F i / s ^ i`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k` is equivalent to
`∑ i ∈ Icc 1 n, f (2 * i - 1) = f (2 * n) / k'` for `k' = k / s` (Batte–Kaggwa, (4.3)). -/
theorem rescale_sum_fib_two_mul_sub_one_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hf : ∀ i, f i = s * F i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k ↔
      ∑ i ∈ Icc 1 n, f (2 * i - 1) = f (2 * n) / (k / s) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (pow_ne_zero n ht) ht (rescale_sum_fib hs hst hf n).2.2.symm ?_
  rw [hf, ← hst]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0` and `f i = s * F i / s ^ i`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k` is equivalent to
`∑ i ∈ Icc 1 n, f (2 * i) = (f (2 * n + 1) - 1) / k'` for `k' = k / s` (Batte–Kaggwa, (4.4)). -/
theorem rescale_sum_fib_two_mul_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hf : ∀ i, f i = s * F i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k ↔
      ∑ i ∈ Icc 1 n, f (2 * i) = (f (2 * n + 1) - 1) / (k / s) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (pow_ne_zero n ht) hs (rescale_sum_fib hs hst hf n).2.1.symm ?_
  rw [hf, ← hst]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0` and `g i = L i / s ^ i`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k` is equivalent to
`∑ i ∈ Icc 1 n, g (2 * i - 1) = (g (2 * n) - 2) / k'` for `k' = k / s` (Batte–Kaggwa, (4.5)). -/
theorem rescale_sum_lucas_two_mul_sub_one_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k ↔
      ∑ i ∈ Icc 1 n, g (2 * i - 1) = (g (2 * n) - 2) / (k / s) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (pow_ne_zero n ht) hs
    (rescale_sum_lucas hs hst hg n).2.2.2.symm ?_
  rw [hg, ← hst]
  field_simp
  ring

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0` and `g i = L i / s ^ i`,
`∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k` is equivalent to
`∑ i ∈ Icc 1 n, g (2 * i) = (g (2 * n + 1) - k') / k'` for `k' = k / s` (Batte–Kaggwa, (4.6)). -/
theorem rescale_sum_lucas_two_mul_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k ↔
      ∑ i ∈ Icc 1 n, g (2 * i) = (g (2 * n + 1) - k / s) / (k / s) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (pow_ne_zero n ht) one_ne_zero
    (by rw [one_mul, (rescale_sum_lucas hs hst hg n).2.2.1]) ?_
  rw [hg, ← hst]
  field_simp
  ring

/-! ### The cross-family bound -/

/-- The right-hand sides of the two cross-family bounds, rescaled. -/
private lemma rescale_cross_rhs (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hf : ∀ i, f i = s * F i / s ^ i) (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    t ^ (2 * n) * (f n * f (n + 1) / (k / s) * ((g n * g (n + 1) - 2 * (k / s)) / (k / s))) =
      t * (F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)) := by
  rw [hf, hf, hg, hg, ← hst]
  field_simp
  ring

/-- The left-hand side of the cross-family bound, rescaled. -/
private lemma rescale_cross_lhs (hs : s ≠ 0) (hst : s ^ 2 = t)
    (hf : ∀ i, f i = s * F i / s ^ i) (n : ℕ) :
    t ^ (2 * n) * (∑ i ∈ Icc 1 n, f (2 * i)) ^ 2 =
      t * (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 := by
  rw [pow_mul', ← mul_pow, ← (rescale_sum_fib hs hst hf n).2.1, mul_pow, hst]

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0`, `f i = s * F i / s ^ i` and `g i = L i / s ^ i`, the
equality `(∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)` is equivalent to
`(∑ i ∈ Icc 1 n, f (2 * i)) ^ 2 = f n * f (n + 1) / k' * ((g n * g (n + 1) - 2 * k') / k')` for
`k' = k / s` (the equality case of Batte–Kaggwa, Theorem 1.5). -/
theorem rescale_sq_sum_fib_two_mul_eq_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hf : ∀ i, f i = s * F i / s ^ i) (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
        F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ↔
      (∑ i ∈ Icc 1 n, f (2 * i)) ^ 2 =
        f n * f (n + 1) / (k / s) * ((g n * g (n + 1) - 2 * (k / s)) / (k / s)) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  exact eq_iff_eq_of_mul_eq (pow_ne_zero _ ht) ht (rescale_cross_lhs hs hst hf n)
    (rescale_cross_rhs hs hst hk hf hg n)

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0`, `f i = s * F i / s ^ i` and `g i = L i / s ^ i`, the
equality `(F (2 * n + 1) - t ^ n) ^ 2 = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)` is
equivalent to
`((f (2 * n + 1) - 1) / k') ^ 2 = f n * f (n + 1) / k' * ((g n * g (n + 1) - 2 * k') / k')` for
`k' = k / s`. -/
theorem rescale_sq_fib_two_mul_add_one_sub_pow_eq_iff (hs : s ≠ 0) (hst : s ^ 2 = t)
    (hk : k ≠ 0) (hf : ∀ i, f i = s * F i / s ^ i) (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    (F (2 * n + 1) - t ^ n) ^ 2 = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) ↔
      ((f (2 * n + 1) - 1) / (k / s)) ^ 2 =
        f n * f (n + 1) / (k / s) * ((g n * g (n + 1) - 2 * (k / s)) / (k / s)) := by
  have ht : t ≠ 0 := hst ▸ pow_ne_zero 2 hs
  refine eq_iff_eq_of_mul_eq (mul_ne_zero (pow_ne_zero (2 * n) ht) (pow_ne_zero 2 hk)) ht ?_ ?_
  · rw [hf, ← hst]
    field_simp
    ring
  · rw [mul_comm (t ^ (2 * n)), mul_assoc, rescale_cross_rhs hs hst hk hf hg n]
    field_simp


end Field

/-! ### The cross-family bound over a linearly ordered field -/

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {k t s : K}
  {F L f g : ℕ → K}

/-- If `c * X' = d * X` and `c * Y' = d * Y` with `c, d > 0`, then `X ≤ Y ↔ X' ≤ Y'`. -/
private lemma le_iff_le_of_mul_eq {c d X Y X' Y' : K} (hc : 0 < c) (hd : 0 < d)
    (hX : c * X' = d * X) (hY : c * Y' = d * Y) : X ≤ Y ↔ X' ≤ Y' := by
  rw [← mul_le_mul_iff_right₀ hd, ← hX, ← hY, mul_le_mul_iff_right₀ hc]

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0`, `f i = s * F i / s ^ i` and `g i = L i / s ^ i`, the
cross-family bound `(∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)` is equivalent to
`(∑ i ∈ Icc 1 n, f (2 * i)) ^ 2 ≤ f n * f (n + 1) / k' * ((g n * g (n + 1) - 2 * k') / k')` for
`k' = k / s` (Batte–Kaggwa, Theorem 1.5). -/
theorem rescale_sq_sum_fib_two_mul_le_iff (hs : s ≠ 0) (hst : s ^ 2 = t) (hk : k ≠ 0)
    (hf : ∀ i, f i = s * F i / s ^ i) (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
        F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ↔
      (∑ i ∈ Icc 1 n, f (2 * i)) ^ 2 ≤
        f n * f (n + 1) / (k / s) * ((g n * g (n + 1) - 2 * (k / s)) / (k / s)) := by
  have ht : 0 < t := hst ▸ lt_of_le_of_ne (sq_nonneg s) (pow_ne_zero 2 hs).symm
  exact le_iff_le_of_mul_eq (pow_pos ht _) ht (rescale_cross_lhs hs hst hf n)
    (rescale_cross_rhs hs hst hk hf hg n)

/-- For `s ≠ 0` with `s ^ 2 = t`, `k ≠ 0`, `f i = s * F i / s ^ i` and `g i = L i / s ^ i`, the
division-free cross-family bound
`(F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)` is equivalent to
`((f (2 * n + 1) - 1) / k') ^ 2 ≤ f n * f (n + 1) / k' * ((g n * g (n + 1) - 2 * k') / k')` for
`k' = k / s` (Batte–Kaggwa, Corollary 4.1). -/
theorem rescale_sq_fib_two_mul_add_one_sub_pow_le_iff (hs : s ≠ 0) (hst : s ^ 2 = t)
    (hk : k ≠ 0) (hf : ∀ i, f i = s * F i / s ^ i) (hg : ∀ i, g i = L i / s ^ i) (n : ℕ) :
    (F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) ↔
      ((f (2 * n + 1) - 1) / (k / s)) ^ 2 ≤
        f n * f (n + 1) / (k / s) * ((g n * g (n + 1) - 2 * (k / s)) / (k / s)) := by
  have ht : 0 < t := hst ▸ lt_of_le_of_ne (sq_nonneg s) (pow_ne_zero 2 hs).symm
  refine le_iff_le_of_mul_eq (mul_pos (pow_pos ht (2 * n)) (lt_of_le_of_ne (sq_nonneg k)
    (pow_ne_zero 2 hk).symm)) ht ?_ ?_
  · rw [hf, ← hst]
    field_simp
    ring
  · rw [mul_comm (t ^ (2 * n)), mul_assoc, rescale_cross_rhs hs hst hk hf hg n]
    field_simp

end OrderedField

/-! ### Real rescaling -/

/-- If `0 ≤ k` and `k ^ 2 < t`, then `k / √t < 1`. -/
theorem div_sqrt_lt_one {k t : ℝ} (hk : 0 ≤ k) (ht : k ^ 2 < t) : k / √t < 1 := by
  rw [div_lt_one (Real.sqrt_pos.2 ((sq_nonneg k).trans_lt ht))]
  exact Real.lt_sqrt hk |>.2 ht

/-- For `0 < t`, `0 ≤ x` and `i ≤ n`, the ratio of `t ^ (n - i) * x ^ α` to `(x / √t ^ i) ^ α` is
`t ^ (n + (α / 2 - 1) * i)`:
`t ^ (n - i) * x ^ α = t ^ (n + (α / 2 - 1) * i) * (x / √t ^ i) ^ α`. -/
theorem pow_sub_mul_rpow_eq {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) {i n : ℕ} (hi : i ≤ n)
    (α : ℝ) : t ^ (n - i) * x ^ α = t ^ ((n : ℝ) + (α / 2 - 1) * i) * (x / √t ^ i) ^ α := by
  have hs : √t ^ i = t ^ ((i : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    ring_nf
  rw [hs, Real.div_rpow hx (by positivity), ← Real.rpow_mul ht.le]
  calc t ^ (n - i) * x ^ α = t ^ ((n : ℝ) - i) * x ^ α := by
        rw [← Real.rpow_natCast, Nat.cast_sub hi]
    _ = t ^ ((n : ℝ) + (α / 2 - 1) * i) * t ^ (-(i / 2 * α)) * x ^ α := by
        rw [← Real.rpow_add ht]
        ring_nf
    _ = _ := by
        rw [Real.rpow_neg ht.le]
        ring

/-- The rescaled Jacobsthal numbers: for the Jacobsthal numbers `J` and the Jacobsthal–Lucas
numbers `j` (the case `(k, t) = (1, 2)`), with `f i = √2 * J i / √2 ^ i` and
`g i = j i / √2 ^ i`, the cross-family bound
`(J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1))` is equivalent to
`((f (2 * n + 1) - 1) / k') ^ 2 ≤ f n * f (n + 1) / k' * ((g n * g (n + 1) - 2 * k') / k')` for
`k' = 1 / √2`, and the corresponding equalities are equivalent. -/
theorem rescale_sq_jacobsthal_two_mul_add_one_sub_pow_iff {J j f g : ℕ → ℝ}
    (hf : ∀ i, f i = √2 * J i / √2 ^ i) (hg : ∀ i, g i = j i / √2 ^ i) (n : ℕ) :
    ((J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ↔
      ((f (2 * n + 1) - 1) / (1 / √2)) ^ 2 ≤
        f n * f (n + 1) / (1 / √2) * ((g n * g (n + 1) - 2 * (1 / √2)) / (1 / √2))) ∧
    ((J (2 * n + 1) - 2 ^ n) ^ 2 = J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ↔
      ((f (2 * n + 1) - 1) / (1 / √2)) ^ 2 =
        f n * f (n + 1) / (1 / √2) * ((g n * g (n + 1) - 2 * (1 / √2)) / (1 / √2))) := by
  have hs : √2 ≠ 0 := by positivity
  have hst : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have e : (2 : ℝ) ^ (n + 1) = 2 * 1 * 2 ^ n := by ring
  rw [e]
  exact ⟨rescale_sq_fib_two_mul_add_one_sub_pow_le_iff hs hst one_ne_zero hf hg n,
    rescale_sq_fib_two_mul_add_one_sub_pow_eq_iff hs hst one_ne_zero hf hg n⟩


end KTFib
