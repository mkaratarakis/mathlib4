/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Set.Monotone
import Mathlib.Order.Interval.Set.Image
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Identities for `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences

Fix `k t` in a commutative ring. The `(k, t)`-Fibonacci sequence `F` and the `(k, t)`-Lucas
sequence `L` are the solutions of the recurrence `X (n + 2) = k * X (n + 1) + t * X n` with
initial values `F 0 = 0`, `F 1 = 1` and `L 0 = 2`, `L 1 = k`. They are the Lucas sequences
`U(k, -t)` and `V(k, -t)`; the `k`-Fibonacci numbers of Falcón and Plaza and the `k`-Lucas numbers
of Falcón are the case `t = 1`, and the Jacobsthal numbers the case `(k, t) = (1, 2)`. The
sequence `L` is the Dickson polynomial `Polynomial.dickson 1 (-t)` evaluated at `k`, and
`n ↦ F (n + 1)` is `Polynomial.dickson 2 (-t)` evaluated at `k` (`Polynomial.eval_dickson_one_eq`,
`Polynomial.eval_dickson_two_eq_add_one`).

No new definition is introduced: every statement takes the sequences as functions `ℕ → R`,
together with the recurrence and the relevant initial values as hypotheses. The file has four
layers.

* Over a commutative ring, for **every** solution `G` of the recurrence: weighted sums with
  weight `t ^ (n - i)` over `i ∈ Finset.Icc 1 n`, Cassini's identity, and the linear sums. The
  statements are division-free, and the right-hand sides involve `G` only at the top indices and
  through the boundary values `G 0`, `G 1` and `G 2 = k * G 1 + t * G 0`.
* Over a commutative ring, identities that fix initial values: `L` in terms of `F`, the addition
  formula for `F`, and the product formula `G (n + m) * L m = G (n + 2 * m) + (-t) ^ m * G n`
  with its consequences `F i * L i = F (2 * i)`, `L m ^ 2 = L (2 * m) + 2 * (-t) ^ m` and
  `L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i`.
* Over a field: the closed forms of the sums for `F` and `L`, dividing by `k` or by `k + t - 1`.
* Over a linearly ordered commutative ring: positivity of `F` and `L`, monotonicity of `L`
  and of `i ↦ L i * L (i + 1)` on `Set.Ici 1`, and the bound
  `L i ^ 2 ≤ ∑ j ∈ Icc 1 n, t ^ (n - j) * L j ^ 2` for `1 ≤ i ≤ n`.

The weight `t ^ (n - i)` is what makes the sums telescope when `t ≠ 1`; at `t = 1` it disappears
and the closed forms reduce to those of Batte and Kaggwa for the `k`-Fibonacci and `k`-Lucas
numbers.

## Main results

* `KTFib.mul_sum_Icc_pow_mul_sq`:
  `k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1`.
* `KTFib.mul_add_two_sub_sq` (Cassini's identity):
  `G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2)`.
* `KTFib.mul_lucas`: `G (n + m) * L m = G (n + 2 * m) + (-t) ^ m * G n`.
* `KTFib.fib_add`: `F (m + n + 1) = F (m + 1) * F (n + 1) + t * F m * F n`.
* `KTFib.sum_pow_mul_lucas_sq`, `KTFib.sum_pow_mul_fib_sq`,
  `KTFib.sum_pow_mul_lucas_mul_lucas_succ`, `KTFib.sum_fib`, `KTFib.sum_lucas`, ...: closed forms
  over a field.
* `KTFib.lucas_strictMonoOn`, `KTFib.lucas_monotoneOn`,
  `KTFib.lucas_mul_lucas_succ_monotoneOn`: monotonicity from index `1` on, and
  `KTFib.lucas_mem_Icc`, `KTFib.lucas_mul_lucas_succ_mem_Icc`: for `1 ≤ i ≤ n`, the values at `i`
  lie between those at `1` and at `n`.
* `KTFib.lucas_sq_le_sum_pow_mul_lucas_sq`: for `1 ≤ k` and `0 ≤ t`, every `L i ^ 2` with
  `1 ≤ i ≤ n` is at most `∑ j ∈ Icc 1 n, t ^ (n - j) * L j ^ 2`.
* `KFib.add_two_eq_mul_add_one_mul`: the recurrence `X (n + 2) = k * X (n + 1) + X n` of the
  `k`-Fibonacci and `k`-Lucas numbers, written as the `(k, 1)`-recurrence.

## References

* [S. Falcón and Á. Plaza, *The `k`-Fibonacci sequence and the Pascal
  2-triangle*][falcon_plaza_2007]
* [S. Falcón, *On the `k`-Lucas numbers*][falcon_2011]
* [H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder
  inequality*][batte_kaggwa_2026]
* [R. Lidl, G. L. Mullen and G. Turnwald, *Dickson polynomials*][MR1237403]
-/

public section

open Finset

/-- Peeling off the top term of a sum weighted by `t ^ (n - i)`: for `a ≤ n + 1`,
`∑ i ∈ Icc a (n + 1), t ^ (n + 1 - i) * f i = t * ∑ i ∈ Icc a n, t ^ (n - i) * f i + f (n + 1)`.
-/
theorem Finset.sum_Icc_succ_top_pow_sub_mul {R : Type*} [CommSemiring R] (t : R) (f : ℕ → R)
    {a n : ℕ} (ha : a ≤ n + 1) :
    ∑ i ∈ Icc a (n + 1), t ^ (n + 1 - i) * f i =
      t * ∑ i ∈ Icc a n, t ^ (n - i) * f i + f (n + 1) := by
  rw [sum_Icc_succ_top ha, mul_sum, Nat.sub_self, pow_zero, one_mul]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  rw [Nat.sub_add_comm (mem_Icc.1 hi).2, pow_succ]
  ring

namespace KTFib

section CommRing

variable {R : Type*} [CommRing R] {k t : R} {G : ℕ → R}

/-- For a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`, the squares weighted by
`t ^ (n - i)` telescope:
`k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1`. -/
theorem mul_sum_Icc_pow_mul_sq (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top_pow_sub_mul t _ (by omega)]
    linear_combination t * ih - G (n + 1) * hG n

/-- **Cassini's identity** for a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`:
`G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2)`. -/
theorem mul_add_two_sub_sq (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (i : ℕ) :
    G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2) := by
  induction i with
  | zero => simp
  | succ i ih => linear_combination (-t) * ih + G (i + 1) * hG (i + 1) - G (i + 2) * hG i

/-- For a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`, the consecutive products
weighted by `t ^ (n - i)` satisfy the division-free identity
`2 * k * ∑ i ∈ Icc 1 n, t ^ (n - i) * (G i * G (i + 1)) =
2 * G (n + 1) ^ 2 - 2 * t ^ n * G 1 ^ 2 + t ^ n * (G 0 * G 2 - G 1 ^ 2) * ((-1) ^ n - 1)`. -/
theorem two_mul_mul_sum_Icc_pow_mul_mul_succ (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n)
    (n : ℕ) :
    2 * k * ∑ i ∈ Icc 1 n, t ^ (n - i) * (G i * G (i + 1)) =
      2 * G (n + 1) ^ 2 - 2 * t ^ n * G 1 ^ 2
        + t ^ n * (G 0 * G 2 - G 1 ^ 2) * ((-1) ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hC := mul_add_two_sub_sq hG n
    rw [neg_pow] at hC
    rw [sum_Icc_succ_top_pow_sub_mul t _ (by omega)]
    linear_combination t * ih - 2 * t * hC - 2 * G (n + 2) * hG n

/-- For a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`, the unweighted linear sum
satisfies `(k + t - 1) * ∑ i ∈ Icc 1 n, G i = G (n + 1) + t * G n - G 1 - t * G 0`. -/
theorem add_sub_one_mul_sum_Icc (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    (k + t - 1) * ∑ i ∈ Icc 1 n, G i = G (n + 1) + t * G n - G 1 - t * G 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    linear_combination ih - hG n

/-- For a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`, the odd-indexed terms weighted
by `t ^ (n - i)` satisfy `k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i - 1) = G (2 * n) - t ^ n * G 0`.
-/
theorem mul_sum_Icc_pow_mul_two_mul_sub_one (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n)
    (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i - 1) = G (2 * n) - t ^ n * G 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top_pow_sub_mul t _ (by omega), show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    linear_combination (norm := ring_nf) t * ih - hG (2 * n)

/-- For a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`, the even-indexed terms weighted
by `t ^ (n - i)` satisfy `k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i) = G (2 * n + 1) - t ^ n * G 1`.
-/
theorem mul_sum_Icc_pow_mul_two_mul (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i) = G (2 * n + 1) - t ^ n * G 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top_pow_sub_mul t _ (by omega)]
    linear_combination (norm := ring_nf) t * ih - hG (2 * n + 1)

variable {F L : ℕ → R}

/-- The `(k, t)`-Lucas sequence in terms of the `(k, t)`-Fibonacci sequence:
`L (n + 1) = F (n + 2) + t * F n`. -/
theorem lucas_add_one_eq_fib_add_two_add_mul_fib (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    L (n + 1) = F (n + 2) + t * F n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hL1, hF, hF0, hF1]
  | one => simp [hL, hF, hL0, hL1, hF0, hF1, mul_two, add_assoc]
  | more n ih1 ih2 => linear_combination hL (n + 1) + k * ih2 + t * ih1 - hF (n + 2) - t * hF n

/-- The addition formula for the `(k, t)`-Fibonacci sequence:
`F (m + n + 1) = F (m + 1) * F (n + 1) + t * F m * F n`. -/
theorem fib_add (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (m n : ℕ) : F (m + n + 1) = F (m + 1) * F (n + 1) + t * F m * F n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hF0, hF1]
  | one => simp [hF, hF0, hF1, mul_comm]
  | more n ih1 ih2 =>
    linear_combination hF (m + n + 1) + k * ih2 + t * ih1 - F (m + 1) * hF (n + 1) - t * F m * hF n

/-- For `k = 0`, the `(k, t)`-Fibonacci numbers of even index vanish: if `F 0 = 0` and
`F (n + 2) = 0 * F (n + 1) + t * F n`, then `F (2 * m) = 0`. -/
theorem fib_two_mul_eq_zero (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = 0 * F (n + 1) + t * F n)
    (m : ℕ) : F (2 * m) = 0 := by
  induction m with
  | zero => exact hF0
  | succ m ih => rw [Nat.mul_succ, hF, ih, zero_mul, mul_zero, add_zero]

/-- Multiplying a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n` by the
`(k, t)`-Lucas sequence: `G (n + m) * L m = G (n + 2 * m) + (-t) ^ m * G n`. -/
theorem mul_lucas (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (m n : ℕ) :
    G (n + m) * L m = G (n + 2 * m) + (-t) ^ m * G n := by
  induction m using Nat.twoStepInduction generalizing n with
  | zero => simp [hL0, mul_two]
  | one => linear_combination (norm := ring_nf) G (n + 1) * hL1 - hG n
  | more m ih1 ih2 =>
    linear_combination (norm := ring_nf) G (n + (m + 2)) * hL m + k * ih2 (n + 1)
      + t * ih1 (n + 2) - hG (n + 2 * m + 2) + t * (-t) ^ m * hG n

/-- `F i * L i = F (2 * i)` for the `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences. -/
theorem fib_mul_lucas (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (i : ℕ) :
    F i * L i = F (2 * i) := by
  simpa [hF0] using mul_lucas hF hL0 hL1 hL i 0

/-- `L m ^ 2 = L (2 * m) + 2 * (-t) ^ m` for the `(k, t)`-Lucas sequence. -/
theorem lucas_sq (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (m : ℕ) : L m ^ 2 = L (2 * m) + 2 * (-t) ^ m := by
  linear_combination (norm := ring_nf) mul_lucas hL hL0 hL1 hL m 0 + (-t) ^ m * hL0

/-- `L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i` for the `(k, t)`-Lucas sequence. -/
theorem lucas_mul_lucas_succ (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (i : ℕ) :
    L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i := by
  linear_combination (norm := ring_nf) mul_lucas hL hL0 hL1 hL i 1 + (-t) ^ i * hL1

end CommRing

/-! ### Closed forms over a field -/

section Field

variable {K : Type*} [Field K] {k t : K} {F L : ℕ → K}

/-- For `k ≠ 0`:
`∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = (L n * L (n + 1) - 2 * k * t ^ n) / k`. -/
theorem sum_pow_mul_lucas_sq (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L i ^ 2 = (L n * L (n + 1) - 2 * k * t ^ n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_sq hL, hL0, hL1]
  ring

/-- For `k ≠ 0`: `∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k`. -/
theorem sum_pow_mul_fib_sq (hk : k ≠ 0) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F i ^ 2 = F n * F (n + 1) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_sq hF, hF0]
  ring

/-- For `k ≠ 0` and `2 ≠ 0`: `∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
(L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k`. -/
theorem sum_pow_mul_lucas_mul_lucas_succ [NeZero (2 : K)] (hk : k ≠ 0) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
      (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k := by
  have h := two_mul_mul_sum_Icc_pow_mul_mul_succ hL n
  rw [hL 0, hL0, hL1] at h
  rw [eq_div_iff hk]
  linear_combination (norm := skip) h / 2
  field_simp
  ring

/-- For `k + t ≠ 1`: `∑ i ∈ Icc 1 n, F i = (F (n + 1) + t * F n - 1) / (k + t - 1)`. -/
theorem sum_fib (hkt : k + t ≠ 1) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i = (F (n + 1) + t * F n - 1) / (k + t - 1) := by
  rw [eq_div_iff (sub_ne_zero.2 hkt), mul_comm, add_sub_one_mul_sum_Icc hF, hF0, hF1]
  ring

/-- For `k + t ≠ 1`: `∑ i ∈ Icc 1 n, L i = (L (n + 1) + t * L n - k - 2 * t) / (k + t - 1)`. -/
theorem sum_lucas (hkt : k + t ≠ 1) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i = (L (n + 1) + t * L n - k - 2 * t) / (k + t - 1) := by
  rw [eq_div_iff (sub_ne_zero.2 hkt), mul_comm, add_sub_one_mul_sum_Icc hL, hL0, hL1]
  ring

/-- For `k ≠ 0`: `∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k`. -/
theorem sum_pow_mul_fib_two_mul_sub_one (hk : k ≠ 0) (hF0 : F 0 = 0)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i - 1) = F (2 * n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_two_mul_sub_one hF, hF0]
  ring

/-- `∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k`. For `k = 0` both
sides vanish. -/
theorem sum_pow_mul_fib_two_mul (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * F (2 * i) = (F (2 * n + 1) - t ^ n) / k := by
  obtain rfl | hk := eq_or_ne k 0
  · simp [fib_two_mul_eq_zero hF0 hF]
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_two_mul hF, hF1]
  ring

/-- For `k ≠ 0`: `∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k`. -/
theorem sum_pow_mul_lucas_two_mul_sub_one (hk : k ≠ 0) (hL0 : L 0 = 2)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_two_mul_sub_one hL, hL0]
  ring

/-- For `k ≠ 0`: `∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k`. -/
theorem sum_pow_mul_lucas_two_mul (hk : k ≠ 0) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i) = (L (2 * n + 1) - k * t ^ n) / k := by
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_two_mul hL, hL1]
  ring

end Field

/-! ### Positivity and monotonicity over a linearly ordered ring -/

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {k t : R}
  {F L : ℕ → R}

/-- For `0 < k` and `0 ≤ t`, the `(k, t)`-Lucas numbers are positive. -/
theorem lucas_pos (hk : 0 < k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) : 0 < L n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hL0]
  | one => rwa [hL1]
  | more n ih1 ih2 =>
    rw [hL n]
    exact add_pos_of_pos_of_nonneg (mul_pos hk ih2) (mul_nonneg ht ih1.le)

/-- For `0 < k` and `0 ≤ t`, the `(k, t)`-Fibonacci numbers of positive index are positive. -/
theorem fib_pos (hk : 0 < k) (ht : 0 ≤ t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) {n : ℕ} (hn : n ≠ 0) : 0 < F n := by
  have key : ∀ m, 0 ≤ F m ∧ 0 < F (m + 1) := by
    intro m
    induction m with
    | zero => simp [hF0, hF1]
    | succ m ih =>
      exact ⟨ih.2.le,
        (add_pos_of_pos_of_nonneg (mul_pos hk ih.2) (mul_nonneg ht ih.1)).trans_eq (hF m).symm⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact (key m).2

/-- For `1 ≤ k` and `0 ≤ t`, `L i ≤ L (i + 1)` for `1 ≤ i`. -/
theorem lucas_le_lucas_succ (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : L i ≤ L (i + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  linarith [hL j, mul_nonneg (sub_nonneg.2 hk) (lucas_pos hk0 ht hL0 hL1 hL (j + 1)).le,
    mul_nonneg ht (lucas_pos hk0 ht hL0 hL1 hL j).le]

/-- For `1 ≤ k` and `0 < t`, `L i < L (i + 1)` for `1 ≤ i`. -/
theorem lucas_lt_lucas_succ (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : L i < L (i + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  linarith [hL j, mul_nonneg (sub_nonneg.2 hk) (lucas_pos hk0 ht.le hL0 hL1 hL (j + 1)).le,
    mul_pos ht (lucas_pos hk0 ht.le hL0 hL1 hL j)]

/-- For `1 ≤ k` and `0 < t`, the `(k, t)`-Lucas numbers are strictly increasing from index `1`
on. -/
theorem lucas_strictMonoOn (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) : StrictMonoOn L (Set.Ici 1) :=
  fun _ hi _ _ hij ↦ Nat.rel_of_forall_rel_succ_of_le_of_lt (f := L) (· < ·)
    (fun _ hn ↦ lucas_lt_lucas_succ hk ht hL0 hL1 hL hn) hi hij

/-- For `1 ≤ k` and `0 ≤ t`, the `(k, t)`-Lucas numbers are increasing from index `1` on. -/
theorem lucas_monotoneOn (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) : MonotoneOn L (Set.Ici 1) :=
  monotoneOn_nat_Ici_of_le_succ fun _ hn ↦ lucas_le_lucas_succ hk ht hL0 hL1 hL hn

/-- For `1 ≤ k` and `0 ≤ t`, `1 ≤ L i` for `1 ≤ i`. -/
theorem one_le_lucas (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : 1 ≤ L i :=
  hk.trans (hL1.symm.trans_le (lucas_monotoneOn hk ht hL0 hL1 hL Set.self_mem_Ici hi hi))

/-- For `1 ≤ k` and `0 ≤ t`, the products `L i * L (i + 1)` are increasing from index `1` on. -/
theorem lucas_mul_lucas_succ_monotoneOn (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) :
    MonotoneOn (fun i ↦ L i * L (i + 1)) (Set.Ici 1) := by
  have hL' := lucas_monotoneOn hk ht hL0 hL1 hL
  have hpos := fun i ↦ (lucas_pos (zero_lt_one.trans_le hk) ht hL0 hL1 hL i).le
  exact hL'.mul (fun i hi j hj hij ↦ hL' (Nat.le_succ_of_le hi) (Nat.le_succ_of_le hj) (by omega))
    (fun i _ ↦ hpos i) fun i _ ↦ hpos (i + 1)

/-- For `1 ≤ k` and `0 ≤ t`, `L i` lies between `L 1` and `L n` for every `i ∈ Icc 1 n`. -/
theorem lucas_mem_Icc (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i n : ℕ} (hi : i ∈ Icc 1 n) :
    L i ∈ Set.Icc (L 1) (L n) :=
  (MonotoneOn.mono (lucas_monotoneOn hk ht hL0 hL1 hL) Set.Icc_subset_Ici_self).mapsTo_Icc
    (Set.mem_Icc.2 (mem_Icc.1 hi))

/-- For `1 ≤ k` and `0 ≤ t`, `L i * L (i + 1)` lies between `L 1 * L 2` and `L n * L (n + 1)` for
every `i ∈ Icc 1 n`. -/
theorem lucas_mul_lucas_succ_mem_Icc (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i n : ℕ} (hi : i ∈ Icc 1 n) :
    L i * L (i + 1) ∈ Set.Icc (L 1 * L 2) (L n * L (n + 1)) :=
  (MonotoneOn.mono (lucas_mul_lucas_succ_monotoneOn hk ht hL0 hL1 hL)
    Set.Icc_subset_Ici_self).mapsTo_Icc
    (Set.mem_Icc.2 (mem_Icc.1 hi))

/-- For `1 ≤ k` and `0 < t`, the products `L i * L (i + 1)` are strictly increasing from index
`1` on. -/
theorem lucas_mul_lucas_succ_strictMonoOn (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) :
    StrictMonoOn (fun i ↦ L i * L (i + 1)) (Set.Ici 1) := fun i hi j hj hij ↦
  have hL' := lucas_strictMonoOn hk ht hL0 hL1 hL
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  mul_lt_mul'' (hL' hi hj hij) (hL' (Nat.le_succ_of_le hi) (Nat.le_succ_of_le hj) (by omega))
    (lucas_pos hk0 ht.le hL0 hL1 hL _).le (lucas_pos hk0 ht.le hL0 hL1 hL _).le

/-- For `1 ≤ k` and `0 ≤ t`, every `L i ^ 2` with `1 ≤ i ≤ n` is at most the weighted sum of
squares `∑ j ∈ Icc 1 n, t ^ (n - j) * L j ^ 2`. -/
theorem lucas_sq_le_sum_pow_mul_lucas_sq (hk : 1 ≤ k) (ht : 0 ≤ t) (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i n : ℕ}
    (hi : i ∈ Icc 1 n) : L i ^ 2 ≤ ∑ j ∈ Icc 1 n, t ^ (n - j) * L j ^ 2 := by
  obtain ⟨h1, h2⟩ := mem_Icc.1 hi
  calc L i ^ 2 ≤ t ^ (n - n) * L n ^ 2 := by
        rw [Nat.sub_self, pow_zero, one_mul]
        exact pow_le_pow_left₀ (lucas_pos (zero_lt_one.trans_le hk) ht hL0 hL1 hL i).le
          (lucas_mem_Icc hk ht hL0 hL1 hL hi).2 2
    _ ≤ _ := single_le_sum (f := fun j ↦ t ^ (n - j) * L j ^ 2)
        (fun j _ ↦ mul_nonneg (pow_nonneg ht _) (sq_nonneg _)) (mem_Icc.2 ⟨h1.trans h2, le_rfl⟩)

end LinearOrder

end KTFib

/-- The recurrence `G (n + 2) = k * G (n + 1) + G n` of the `k`-Fibonacci and `k`-Lucas numbers is
the `(k, 1)`-recurrence `G (n + 2) = k * G (n + 1) + 1 * G n`, so that the `(k, t)` results apply
at `t = 1`. -/
theorem KFib.add_two_eq_mul_add_one_mul {R : Type*} [Semiring R] {k : R} {G : ℕ → R}
    (hG : ∀ n, G (n + 2) = k * G (n + 1) + G n) (n : ℕ) :
    G (n + 2) = k * G (n + 1) + 1 * G n := by
  rw [hG n, one_mul]
