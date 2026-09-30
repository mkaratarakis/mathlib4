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

* `KTFib.mul_sum_sq`:
  `k * ∑ i ∈ [1, n], t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1`.
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

private theorem sum_Icc_step (f : ℕ → R) (n : ℕ) :
    ∑ i ∈ Icc 1 (n + 1), t ^ (n + 1 - i) * f i =
      t * ∑ i ∈ Icc 1 n, t ^ (n - i) * f i + f (n + 1) := by
  rw [sum_Icc_succ_top (by omega), mul_sum, Nat.sub_self, pow_zero, one_mul]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [mem_Icc] at hi
  rw [show n + 1 - i = n - i + 1 by omega, pow_succ]
  ring

/-- Weighted sum of squares of a solution of `G (n + 2) = k * G (n + 1) + t * G n`. -/
theorem mul_sum_sq (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : G (n + 1 + 1) = k * G (n + 1) + t * G n := hG n
    rw [sum_Icc_step]
    linear_combination t * ih - G (n + 1) * h

/-- Cassini's identity for a solution of the `(k, t)` recurrence. -/
theorem cassini (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (i : ℕ) :
    G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : G (i + 3) = k * G (i + 2) + t * G (i + 1) := hG (i + 1)
    change G (i + 1) * G (i + 3) - G (i + 2) ^ 2 = _
    linear_combination (-t) * ih + G (i + 1) * h1 - G (i + 2) * hG i

/-- Weighted sum of consecutive products of a solution of the `(k, t)` recurrence, in the
division-free form: `2 * k * ∑ t ^ (n - i) * G i * G (i + 1)` equals
`2 * G (n + 1) ^ 2 - 2 * t ^ n * G 1 ^ 2 + t ^ n * (G 0 * G 2 - G 1 ^ 2) * ((-1) ^ n - 1)`. -/
theorem two_mul_mul_sum_mul_succ (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    2 * k * ∑ i ∈ Icc 1 n, t ^ (n - i) * (G i * G (i + 1)) =
      2 * G (n + 1) ^ 2 - 2 * t ^ n * G 1 ^ 2
        + t ^ n * (G 0 * G 2 - G 1 ^ 2) * ((-1) ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : G (n + 1 + 1) = k * G (n + 1) + t * G n := hG n
    have hC : G n * G (n + 1 + 1) - G (n + 1) ^ 2 =
        (-1) ^ n * t ^ n * (G 0 * G 2 - G 1 ^ 2) := by
      rw [← neg_pow]; exact cassini hG n
    rw [sum_Icc_step]
    linear_combination t * ih - 2 * t * hC - 2 * G (n + 1 + 1) * h

/-- Unweighted linear sum of a solution of the `(k, t)` recurrence. -/
theorem mul_sum (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    (k + t - 1) * ∑ i ∈ Icc 1 n, G i = G (n + 1) + t * G n - G 1 - t * G 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : G (n + 1 + 1) = k * G (n + 1) + t * G n := hG n
    rw [sum_Icc_succ_top (by omega)]
    linear_combination ih - h

/-- Weighted sum of the odd-indexed terms of a solution of the `(k, t)` recurrence. -/
theorem mul_sum_odd (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i - 1) = G (2 * n) - t ^ n * G 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_step, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      show 2 * (n + 1) = 2 * n + 2 by ring]
    linear_combination t * ih - hG (2 * n)

/-- Weighted sum of the even-indexed terms of a solution of the `(k, t)` recurrence. -/
theorem mul_sum_even (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G (2 * i) = G (2 * n + 1) - t ^ n * G 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : G (2 * n + 3) = k * G (2 * n + 2) + t * G (2 * n + 1) := hG (2 * n + 1)
    rw [sum_Icc_step, show 2 * (n + 1) + 1 = 2 * n + 3 by ring,
      show 2 * (n + 1) = 2 * n + 2 by ring]
    linear_combination t * ih - h

variable {F L : ℕ → R}

/-- The `(k, t)`-Lucas sequence in terms of the `(k, t)`-Fibonacci sequence. -/
theorem lucas_eq (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    L (n + 1) = F (n + 2) + t * F n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have h2 : F 2 = k * F 1 + t * F 0 := hF 0
    change L 1 = F 2 + t * F 0
    rw [h2, hL1, hF0, hF1]; ring
  | one =>
    have h2 : F 2 = k * F 1 + t * F 0 := hF 0
    have h3 : F 3 = k * F 2 + t * F 1 := hF 1
    have l2 : L 2 = k * L 1 + t * L 0 := hL 0
    change L 2 = F 3 + t * F 1
    rw [l2, h3, h2, hL1, hL0, hF0, hF1]; ring
  | more n ih1 ih2 =>
    have l3 : L (n + 3) = k * L (n + 2) + t * L (n + 1) := hL (n + 1)
    have h4 : F (n + 4) = k * F (n + 3) + t * F (n + 2) := hF (n + 2)
    have h2 : F (n + 2) = k * F (n + 1) + t * F n := hF n
    have ih2' : L (n + 2) = F (n + 3) + t * F (n + 1) := ih2
    change L (n + 3) = F (n + 4) + t * F (n + 2)
    linear_combination l3 + k * ih2' + t * ih1 - h4 - t * h2

/-- Addition formula `F (m + n + 1) = F (m + 1) * F (n + 1) + t * F m * F n`. -/
private theorem fib_add (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (m n : ℕ) :
    F (m + n + 1) = F (m + 1) * F (n + 1) + t * F m * F n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hF0, hF1]
  | one =>
    have h2 : F 2 = k * F 1 + t * F 0 := hF 0
    have hm : F (m + 2) = k * F (m + 1) + t * F m := hF m
    change F (m + 2) = F (m + 1) * F 2 + t * F m * F 1
    rw [hm, h2, hF0, hF1]; ring
  | more n ih1 ih2 =>
    have h1 : F (m + n + 3) = k * F (m + n + 2) + t * F (m + n + 1) := hF (m + n + 1)
    have h2 : F (n + 3) = k * F (n + 2) + t * F (n + 1) := hF (n + 1)
    have ih2' : F (m + n + 2) = F (m + 1) * F (n + 2) + t * F m * F (n + 1) := ih2
    change F (m + n + 3) = F (m + 1) * F (n + 3) + t * F m * F (n + 2)
    linear_combination h1 + k * ih2' + t * ih1 - F (m + 1) * h2 - t * F m * hF n

/-- The cross identity `F i * L i = F (2 * i)`. -/
theorem fib_mul_lucas (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (i : ℕ) :
    F i * L i = F (2 * i) := by
  rcases i with _ | j
  · simp [hF0]
  · have hA : F (2 * (j + 1)) = F (j + 2) * F (j + 1) + t * F (j + 1) * F j := by
      rw [show 2 * (j + 1) = (j + 1) + j + 1 by ring]
      exact fib_add hF0 hF1 hF (j + 1) j
    rw [lucas_eq hF0 hF1 hF hL0 hL1 hL, hA]
    ring

/-- `L m ^ 2`, `L m * L (m + 1)` and `L (m + 1) ^ 2`, proved simultaneously. -/
private theorem lucas_triple (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (m : ℕ) :
    L m ^ 2 = L (2 * m) + 2 * (-t) ^ m ∧
      L m * L (m + 1) = L (2 * m + 1) + k * (-t) ^ m ∧
      L (m + 1) ^ 2 = L (2 * m + 2) + 2 * (-t) ^ (m + 1) := by
  induction m with
  | zero =>
    have l2 : L 2 = k * L 1 + t * L 0 := hL 0
    change L 0 ^ 2 = L 0 + 2 * (-t) ^ 0 ∧ L 0 * L 1 = L 1 + k * (-t) ^ 0 ∧
      L 1 ^ 2 = L 2 + 2 * (-t) ^ (0 + 1)
    rw [l2, hL0, hL1]
    refine ⟨by ring, by ring, by ring⟩
  | succ m ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have e1 : L (m + 2) = k * L (m + 1) + t * L m := hL m
    have e2 : L (2 * m + 3) = k * L (2 * m + 2) + t * L (2 * m + 1) := hL (2 * m + 1)
    have e3 : L (2 * m + 4) = k * L (2 * m + 3) + t * L (2 * m + 2) := hL (2 * m + 2)
    have e4 : L (2 * m + 2) = k * L (2 * m + 1) + t * L (2 * m) := hL (2 * m)
    change L (m + 1) ^ 2 = L (2 * m + 2) + 2 * (-t) ^ (m + 1) ∧
      L (m + 1) * L (m + 2) = L (2 * m + 3) + k * (-t) ^ (m + 1) ∧
      L (m + 2) ^ 2 = L (2 * m + 4) + 2 * (-t) ^ (m + 2)
    refine ⟨hC, ?_, ?_⟩
    · linear_combination L (m + 1) * e1 + k * hC + t * hB - e2
    · linear_combination (L (m + 2) + k * L (m + 1) + t * L m) * e1 + k ^ 2 * hC
        + 2 * k * t * hB + t ^ 2 * hA - e3 - k * e2 - t * e4

/-- `L m ^ 2 = L (2 * m) + 2 * (-t) ^ m`. -/
theorem lucas_sq (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n)
    (m : ℕ) : L m ^ 2 = L (2 * m) + 2 * (-t) ^ m :=
  (lucas_triple hL0 hL1 hL m).1

/-- `L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i`. -/
theorem lucas_mul_succ (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (i : ℕ) :
    L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i :=
  (lucas_triple hL0 hL1 hL i).2.1

/-- The `(k, t)`-Lucas sequence is the Dickson polynomial of the first kind with parameter
`-t`, evaluated at `k`. -/
theorem dickson_one_eval (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    (Polynomial.dickson 1 (-t) n).eval k = L n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [hL0, Polynomial.dickson_zero]
  | one => simp [hL1]
  | more n ih1 ih2 =>
    rw [Polynomial.dickson_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, ih1, ih2, hL n]
    ring

/-- The `(k, t)`-Fibonacci sequence is the shifted Dickson polynomial of the second kind with
parameter `-t`, evaluated at `k`. -/
theorem dickson_two_eval (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (n : ℕ) :
    (Polynomial.dickson 2 (-t) n).eval k = F (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [hF1, Polynomial.dickson_zero]
  | one =>
    have h2 : F 2 = k * F 1 + t * F 0 := hF 0
    change (Polynomial.dickson 2 (-t) 1).eval k = F 2
    rw [h2, hF1, hF0]; simp
  | more n ih1 ih2 =>
    have h : F (n + 2 + 1) = k * F (n + 1 + 1) + t * F (n + 1) := hF (n + 1)
    rw [Polynomial.dickson_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, ih1, ih2, h]
    ring

end CommRing

section Real

variable {k t : ℝ} {F L : ℕ → ℝ}

/-- For `k > 0` and `t > 0`, the `(k, t)`-Lucas numbers are positive. -/
theorem lucas_pos (hk : 0 < k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) : 0 < L n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [hL0]; norm_num
  | one => rwa [hL1]
  | more n ih1 ih2 => rw [hL n]; exact add_pos (mul_pos hk ih2) (mul_pos ht ih1)

/-- For `k > 0` and `t > 0`, the `(k, t)`-Fibonacci numbers of positive index are positive. -/
theorem fib_pos (hk : 0 < k) (ht : 0 < t) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) {n : ℕ} (hn : n ≠ 0) : 0 < F n := by
  have key : ∀ m, 0 < F (m + 1) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => change 0 < F 1; rw [hF1]; norm_num
    | one =>
      have h2 : F (1 + 1) = k * F 1 + t * F 0 := hF 0
      rw [h2, hF0, hF1]; simpa using hk
    | more m ih1 ih2 =>
      have h : F (m + 2 + 1) = k * F (m + 1 + 1) + t * F (m + 1) := hF (m + 1)
      rw [h]; exact add_pos (mul_pos hk ih2) (mul_pos ht ih1)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact key m

/-- For `k ≥ 1` and `t > 0`, the `(k, t)`-Lucas numbers are strictly increasing from index `1`
on. -/
theorem lucas_lt_lucas_succ (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : L i < L (i + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 := lucas_pos (by linarith) ht hL0 hL1 hL (j + 1)
  have h0 := lucas_pos (by linarith) ht hL0 hL1 hL j
  have : 0 ≤ (k - 1) * L (j + 1) := mul_nonneg (by linarith) h1.le
  have : 0 < t * L j := mul_pos ht h0
  have h : L (j + 1 + 1) = k * L (j + 1) + t * L j := hL j
  rw [h]
  linarith

/-- For `k ≥ 1` and `t > 0`, the Lucas numbers are strictly monotone from index `1` on. -/
theorem lucas_strictMono (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    L i < L j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  induction d with
  | zero => exact lucas_lt_lucas_succ hk ht hL0 hL1 hL hi
  | succ d ih =>
    exact (ih (by omega)).trans (lucas_lt_lucas_succ hk ht hL0 hL1 hL (by omega))

/-- For `k ≥ 1` and `t > 0`, `L i ≤ L j` whenever `1 ≤ i ≤ j`. -/
theorem lucas_mono (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    L i ≤ L j := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (lucas_strictMono hk ht hL0 hL1 hL hi h).le

/-- For `k ≥ 1` and `t > 0`, `L i ≥ 1` for `i ≥ 1`. -/
theorem one_le_lucas (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i : ℕ} (hi : 1 ≤ i) : 1 ≤ L i := by
  have := lucas_mono hk ht hL0 hL1 hL le_rfl hi
  rw [hL1] at this
  linarith

/-- For `k ≥ 1` and `t > 0`, the consecutive products `L i * L (i + 1)` are monotone from index
`1` on. -/
theorem lucas_mul_mono (hk : 1 ≤ k) (ht : 0 < t) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    L i * L (i + 1) ≤ L j * L (j + 1) := by
  have hk0 : 0 < k := by linarith
  exact mul_le_mul (lucas_mono hk ht hL0 hL1 hL hi hij)
    (lucas_mono hk ht hL0 hL1 hL (by omega) (by omega))
    (lucas_pos hk0 ht hL0 hL1 hL _).le (lucas_pos hk0 ht hL0 hL1 hL _).le


end Real

end KTFib
