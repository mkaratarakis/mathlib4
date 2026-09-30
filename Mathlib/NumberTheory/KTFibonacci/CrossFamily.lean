/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Lagrange
public import Mathlib.NumberTheory.KTFibonacci.Identities

/-!
# A cross-family bound for `(k, t)`-Fibonacci and `(k, t)`-Lucas numbers

Let `F` and `L` be the `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences: `F 0 = 0`, `F 1 = 1`,
`L 0 = 2`, `L 1 = k`, both satisfying `X (n + 2) = k * X (n + 1) + t * X n`. Since
`F (2 * i) = F i * L i` (`KTFib.fib_mul_lucas`), the weighted Cauchy–Schwarz inequality
(`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`) bounds `∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)`
by the weighted sums of squares of `F` and of `L`, which telescope
(`KTFib.mul_sum_Icc_pow_mul_sq`). By the weighted Lagrange identity
(`Finset.two_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq`) the bound is strict as soon as `n ≥ 2` and
`t > 0`.

## Main results

* `KTFib.sq_sum_pow_mul_fib_two_mul_le`: over a linearly ordered field, for `k ≠ 0` and `0 ≤ t`,
  `(∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
  F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)`, and
  `KTFib.sq_sum_pow_mul_fib_two_mul_eq_iff`: for `k ≠ 0`, `0 < t` and `n ≥ 1`, equality holds
  if and only if `n = 1`.
* `KTFib.sq_fib_sub_le`: the division-free form, over a linearly ordered commutative ring, for
  every `k` and `0 ≤ t`:
  `(F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)`, and
  `KTFib.sq_fib_sub_eq_iff`: for `k ≠ 0`, `0 < t` and `n ≥ 1`, equality holds if and only if
  `n = 1`.
* `KTFib.sq_jacobsthal_sub_le`, `KTFib.sq_jacobsthal_sub_eq_iff`: the case `(k, t) = (1, 2)` of
  the Jacobsthal and Jacobsthal–Lucas numbers, over `ℤ`.

At `t = 1` the first two results are Theorem 1.5 and Corollary 4.1 of Batte and Kaggwa (see
`Mathlib.NumberTheory.KTFibonacci.KFibonacci`).

## References

* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
-/

public section

open Finset

namespace KTFib

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {k t : R}
  {F L : ℕ → R}

/-- Cauchy–Schwarz for the weights `t ^ (n - i)`, using `F (2 * i) = F i * L i`. -/
private lemma sq_sum_le_sum_mul_sum (ht : 0 ≤ t) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
      (∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun _ _ ↦ by positivity) (fun _ _ ↦ by positivity)
    fun i _ ↦ le_of_eq (by rw [← fib_mul_lucas hF0 hF hL0 hL1 hL]; ring)

/-- The equality case of the weighted Cauchy–Schwarz bound above, via the Lagrange identity:
the term `(i, j) = (1, 2)` of the Lagrange sum is `t ^ (n - 1) * t ^ (n - 2) * (2 * t) ^ 2 > 0`.
-/
private lemma sq_sum_eq_sum_mul_sum_iff (ht : 0 < t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
        (∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2) * ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 ↔
      n = 1 := by
  simp_rw [← fib_mul_lucas hF0 hF hL0 hL1 hL]
  refine ⟨fun heq ↦ ?_, by rintro rfl; simp; ring⟩
  by_contra h1
  have h := two_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq (Icc 1 n) (fun i ↦ t ^ (n - i)) F L
  have h12 : F 1 * L 2 - F 2 * L 1 = 2 * t := by
    rw [hF 0, hL 0, hF0, hF1, hL0, hL1]
    ring
  have hpos : 0 < ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n,
      t ^ (n - i) * t ^ (n - j) * (F i * L j - F j * L i) ^ 2 := by
    refine sum_pos' (fun i _ ↦ sum_nonneg fun j _ ↦ by positivity)
      ⟨1, mem_Icc.2 ⟨le_rfl, hn⟩, sum_pos' (fun j _ ↦ by positivity)
        ⟨2, mem_Icc.2 ⟨one_le_two, by omega⟩, ?_⟩⟩
    rw [h12]
    positivity
  linarith

/-- The cross-family bound in division-free form: for `0 ≤ t` and any `k`,
`(F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)`. -/
theorem sq_fib_sub_le (ht : 0 ≤ t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    (F (2 * n + 1) - t ^ n) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) := by
  have h := mul_le_mul_of_nonneg_left (sq_sum_le_sum_mul_sum ht hF0 hF hL0 hL1 hL n)
    (sq_nonneg k)
  have e1 := mul_sum_Icc_pow_mul_two_mul hF n
  have e2 := mul_sum_Icc_pow_mul_sq hF n
  have e3 := mul_sum_Icc_pow_mul_sq hL n
  rw [hF1, mul_one] at e1
  rw [hF0, mul_zero, zero_mul, sub_zero] at e2
  rw [hL0, hL1] at e3
  rw [← e1, ← e2, show L n * L (n + 1) - 2 * k * t ^ n = L n * L (n + 1) - t ^ n * 2 * k by ring,
    ← e3]
  linarith

/-- Equality in `KTFib.sq_fib_sub_le`: for `k ≠ 0`, `0 < t` and `n ≥ 1`,
`(F (2 * n + 1) - t ^ n) ^ 2 = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n)` if and only
if `n = 1`. -/
theorem sq_fib_sub_eq_iff (hk : k ≠ 0) (ht : 0 < t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 1 ≤ n) :
    (F (2 * n + 1) - t ^ n) ^ 2 = F n * F (n + 1) * (L n * L (n + 1) - 2 * k * t ^ n) ↔
      n = 1 := by
  have e1 := mul_sum_Icc_pow_mul_two_mul hF n
  have e2 := mul_sum_Icc_pow_mul_sq hF n
  have e3 := mul_sum_Icc_pow_mul_sq hL n
  rw [hF1, mul_one] at e1
  rw [hF0, mul_zero, zero_mul, sub_zero] at e2
  rw [hL0, hL1] at e3
  rw [← e1, ← e2, show L n * L (n + 1) - 2 * k * t ^ n = L n * L (n + 1) - t ^ n * 2 * k by ring,
    ← e3, mul_pow, mul_mul_mul_comm, ← sq, mul_right_inj' (pow_ne_zero 2 hk)]
  exact sq_sum_eq_sum_mul_sum_iff ht hF0 hF1 hF hL0 hL1 hL hn

end LinearOrder

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {k t : K} {F L : ℕ → K}

/-- **Cross-family bound**: for `k ≠ 0` and `0 ≤ t`,
`(∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)`
(Batte–Kaggwa, Theorem 1.5, for `t = 1`). -/
theorem sq_sum_pow_mul_fib_two_mul_le (hk : k ≠ 0) (ht : 0 ≤ t) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 ≤
      F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) := by
  rw [← sum_pow_mul_sq_fib hk hF0 hF, ← sum_pow_mul_sq_lucas hk hL0 hL1 hL]
  exact sq_sum_le_sum_mul_sum ht hF0 hF hL0 hL1 hL n

/-- Equality in `KTFib.sq_sum_pow_mul_fib_two_mul_le`: for `k ≠ 0`, `0 < t` and `n ≥ 1`,
`(∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k)` if and only if `n = 1`
(Batte–Kaggwa, Theorem 1.5, for `t = 1`). -/
theorem sq_sum_pow_mul_fib_two_mul_eq_iff (hk : k ≠ 0) (ht : 0 < t) (hF0 : F 0 = 0)
    (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i)) ^ 2 =
        F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k * t ^ n) / k) ↔ n = 1 := by
  rw [← sum_pow_mul_sq_fib hk hF0 hF, ← sum_pow_mul_sq_lucas hk hL0 hL1 hL]
  exact sq_sum_eq_sum_mul_sum_iff ht hF0 hF1 hF hL0 hL1 hL hn

end Field

/-! ### The Jacobsthal numbers -/

section Jacobsthal

variable {J j : ℕ → ℤ}

/-- The cross-family bound for the Jacobsthal numbers `J` and the Jacobsthal–Lucas numbers `j`
(the case `(k, t) = (1, 2)`):
`(J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1))`. -/
theorem sq_jacobsthal_sub_le (hJ0 : J 0 = 0) (hJ1 : J 1 = 1)
    (hJ : ∀ n, J (n + 2) = J (n + 1) + 2 * J n) (hj0 : j 0 = 2) (hj1 : j 1 = 1)
    (hj : ∀ n, j (n + 2) = j (n + 1) + 2 * j n) (n : ℕ) :
    (J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) := by
  have h := sq_fib_sub_le zero_le_two hJ0 hJ1 (fun n ↦ by rw [hJ, one_mul]) hj0 hj1
    (fun n ↦ by rw [hj, one_mul]) n
  rwa [mul_one, ← pow_succ'] at h

/-- Equality in `KTFib.sq_jacobsthal_sub_le`: for `n ≥ 1`,
`(J (2 * n + 1) - 2 ^ n) ^ 2 = J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1))` if and only if
`n = 1`. -/
theorem sq_jacobsthal_sub_eq_iff (hJ0 : J 0 = 0) (hJ1 : J 1 = 1)
    (hJ : ∀ n, J (n + 2) = J (n + 1) + 2 * J n) (hj0 : j 0 = 2) (hj1 : j 1 = 1)
    (hj : ∀ n, j (n + 2) = j (n + 1) + 2 * j n) {n : ℕ} (hn : 1 ≤ n) :
    (J (2 * n + 1) - 2 ^ n) ^ 2 = J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ↔
      n = 1 := by
  have h := sq_fib_sub_eq_iff one_ne_zero two_pos hJ0 hJ1 (fun n ↦ by rw [hJ, one_mul]) hj0 hj1
    (fun n ↦ by rw [hj, one_mul]) hn
  rwa [mul_one, ← pow_succ'] at h

end Jacobsthal

end KTFib
