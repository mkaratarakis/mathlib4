/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Dickson
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Sum identities for `(k, t)`-Fibonacci and `(k, t)`-Lucas sequences

The `(k, t)`-Fibonacci sequence `F` and the `(k, t)`-Lucas sequence `L` are the solutions of
`X (n + 2) = k * X (n + 1) + t * X n` with initial values `F 0 = 0`, `F 1 = 1` and
`L 0 = 2`, `L 1 = k`.  They are the Lucas sequences `U(k, -t)` and `V(k, -t)`; the
`k`-Fibonacci and `k`-Lucas numbers of Falcón and Plaza are the case `t = 1`, and the
Jacobsthal numbers the case `(k, t) = (1, 2)`.  Viewed with `k` and `t` as indeterminates they
are the bivariate Fibonacci and Lucas polynomials; over `R[X]`, `L` is the Dickson polynomial
`Polynomial.dickson 1 (-t)` evaluated at `k` (`KTFib.dickson_one_eval`).

No new definition is introduced.  Every statement takes a sequence `G : ℕ → R` over an
arbitrary commutative ring together with the recurrence as a hypothesis, and holds for **every**
solution; the two initial values enter only through the boundary terms `G 0` and `G 1`.
Statements are division-free, so they are identities in `ℤ[k, t]`.

## Main results

* `KTFib.mul_sum_sq`: `k * ∑ i ∈ [1, n], t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1`.
* `KTFib.cassini`: `G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2)`.
* `KTFib.two_mul_mul_sum_mul_succ`: the weighted sum of consecutive products.
* `KTFib.fib_mul_lucas`: `F i * L i = F (2 * i)`.
* `KTFib.mul_sum`, `KTFib.mul_sum_odd`, `KTFib.mul_sum_even`: linear sums.
* `KTFib.lucas_pos`, `KTFib.lucas_lt_lucas_succ`, ...: positivity and monotonicity over `ℝ`.

The weight `t ^ (n - i)` is what makes the sums telescope when `t ≠ 1`; it is invisible at
`t = 1`, where the identities reduce to those of Batte and Kaggwa for the `k`-Fibonacci and
`k`-Lucas numbers.
-/

@[expose] public section

open Finset

namespace KTFib

section CommRing

variable {R : Type*} [CommRing R] {k t : R} {G : ℕ → R}

/-- Weighted sum of squares of a solution of `G (n + 2) = k * G (n + 1) + t * G n`. -/
theorem mul_sum_sq (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1 := by
  sorry

/-- Cassini's identity for a solution of the `(k, t)` recurrence. -/
theorem cassini (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (i : ℕ) :
    G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2) := by
  sorry

/-- Weighted sum of consecutive products of a solution of the `(k, t)` recurrence, in the
division-free form: `2 * k * ∑ t ^ (n - i) * G i * G (i + 1)` equals
`2 * G (n + 1) ^ 2 - 2 * t ^ n * G 1 ^ 2 + t ^ n * (G 0 * G 2 - G 1 ^ 2) * ((-1) ^ n - 1)`. -/
theorem two_mul_mul_sum_mul_succ (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    2 * k * ∑ i ∈ Icc 1 n, t ^ (n - i) * (G i * G (i + 1)) =
      2 * G (n + 1) ^ 2 - 2 * t ^ n * G 1 ^ 2
        + t ^ n * (G 0 * G 2 - G 1 ^ 2) * ((-1) ^ n - 1) := by
  sorry

/-- Unweighted linear sum of a solution of the `(k, t)` recurrence. -/
theorem mul_sum (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    (k + t - 1) * ∑ i ∈ Icc 1 n, G i = G (n + 1) + t * G n - G 1 - t * G 0 := by
  sorry

/-- Weighted sum of the odd-indexed terms of a solution of the `(k, t)` recurrence. -/
theorem mul_sum_odd (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i - 1) = G (2 * n) - t ^ n * G 0 := by
  sorry

/-- Weighted sum of the even-indexed terms of a solution of the `(k, t)` recurrence. -/
theorem mul_sum_even (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i) = G (2 * n + 1) - t ^ n * G 1 := by
  sorry

variable {F L : ℕ → R}

/-- The `(k, t)`-Lucas sequence in terms of the `(k, t)`-Fibonacci sequence. -/
theorem lucas_eq (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    L (n + 1) = F (n + 2) + t * F n := by
  sorry

/-- The cross identity `F i * L i = F (2 * i)`. -/
theorem fib_mul_lucas (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (i : ℕ) :
    F i * L i = F (2 * i) := by
  sorry

/-- `L m ^ 2 = L (2 * m) + 2 * (-t) ^ m`. -/
theorem lucas_sq (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (m : ℕ) : L m ^ 2 = L (2 * m) + 2 * (-t) ^ m := by
  sorry

/-- `L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i`. -/
theorem lucas_mul_succ (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (i : ℕ) :
    L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i := by
  sorry

/-- The `(k, t)`-Lucas sequence is the Dickson polynomial of the first kind with parameter
`-t`, evaluated at `k`. -/
theorem dickson_one_eval (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    (Polynomial.dickson 1 (-t) n).eval k = L n := by
  sorry

/-- The `(k, t)`-Fibonacci sequence is the shifted Dickson polynomial of the second kind with
parameter `-t`, evaluated at `k`. -/
theorem dickson_two_eval (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    (Polynomial.dickson 2 (-t) n).eval k = F (n + 1) := by
  sorry

end CommRing

section Real

variable {k t : ℝ} {F L : ℕ → ℝ}

/-- For `k > 0` and `t > 0`, the `(k, t)`-Lucas numbers are positive. -/
theorem lucas_pos (hk : 0 < k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) : 0 < L n := by
  sorry

/-- For `k > 0` and `t > 0`, the `(k, t)`-Fibonacci numbers of positive index are positive. -/
theorem fib_pos (hk : 0 < k) (ht : 0 < t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) {n : ℕ} (hn : n ≠ 0) : 0 < F n := by
  sorry

/-- For `k ≥ 1` and `t > 0`, the `(k, t)`-Lucas numbers are strictly increasing from index `1`
on. -/
theorem lucas_lt_lucas_succ (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : L i < L (i + 1) := by
  sorry

/-- For `k ≥ 1` and `t > 0`, `L i ≤ L j` whenever `1 ≤ i ≤ j`. -/
theorem lucas_mono (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    L i ≤ L j := by
  sorry

/-- For `k ≥ 1` and `t > 0`, `L i ≥ 1` for `i ≥ 1`. -/
theorem one_le_lucas (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : 1 ≤ L i := by
  sorry

/-- For `k ≥ 1` and `t > 0`, the consecutive products `L i * L (i + 1)` are monotone from index
`1` on. -/
theorem lucas_mul_mono (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    L i * L (i + 1) ≤ L j * L (j + 1) := by
  sorry

/-- For `k ≥ 1` and `t > 0`, the Lucas numbers are strictly monotone from index `1` on. -/
theorem lucas_strictMono (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    L i < L j := by
  sorry

end Real

end KTFib
