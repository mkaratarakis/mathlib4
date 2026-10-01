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
together with the recurrence and the relevant initial values as hypotheses. The file has five
layers.

* Over a commutative semiring, the subtraction-free identities: `L` in terms of `F`, the addition
  formula `G (m + n + 1) = G (m + 1) * F (n + 1) + t * G m * F n` for every solution `G`, and the
  vanishing of `F` at even indices when `k = 0`.
* Over a commutative ring, for **every** solution `G` of the recurrence: weighted sums with
  weight `t ^ (n - i)` over `i ∈ Finset.Icc 1 n`, Cassini's identity, and the linear sums. The
  statements are division-free, and the right-hand sides involve `G` only at the top indices and
  through the boundary values `G 0`, `G 1` and `G 2 = k * G 1 + t * G 0`. Up to a constant factor,
  `t ^ (n - i)` is the only weight for which the sums telescope term by term.
* Over a commutative ring, the product formula `G (n + m) * L m = G (n + 2 * m) + (-t) ^ m * G n`
  with its consequences `F i * L i = F (2 * i)`, `L m ^ 2 = L (2 * m) + 2 * (-t) ^ m` and
  `L i * L (i + 1) = L (2 * i + 1) + k * (-t) ^ i`, and the unweighted sum of the `L i ^ 2`.
* Over a field: the closed forms of the sums for `F` and `L`, dividing by `k`, by `k + t - 1` or,
  for the unweighted sum of the `L i ^ 2`, by `k ^ 2 - (t - 1) ^ 2`.
* Over a linearly ordered commutative ring: positivity of `F` and `L` for `0 < k` and `0 ≤ t`,
  and, for `1 ≤ k` and `0 ≤ t`, monotonicity of `L` and of `i ↦ L i * L (i + 1)` on `Set.Ici 1`
  (strict for `0 < t`) and the bound `L i ^ 2 ≤ ∑ j ∈ Icc 1 n, t ^ (n - j) * L j ^ 2` for
  `1 ≤ i ≤ n`.

The weight `t ^ (n - i)` is what makes the sums telescope when `t ≠ 1`; at `t = 1` it disappears
and the closed forms reduce to those of Batte and Kaggwa for the `k`-Fibonacci and `k`-Lucas
numbers.

## Main results

* `KTFib.mul_sum_Icc_pow_mul_sq`:
  `k * ∑ i ∈ Icc 1 n, t ^ (n - i) * G i ^ 2 = G n * G (n + 1) - t ^ n * G 0 * G 1`.
* `KTFib.forall_sum_Icc_mul_sub_mul_eq_iff`: `∑ i ∈ Icc 1 n, c i * (P i - t * P (i - 1))` equals
  `a * P n + b * P 0` for every sequence `P` if and only if `c i = a * t ^ (n - i)` and
  `b = -(a * t ^ n)`; `KTFib.mul_sum_Icc_one_three_mul_sq`: other weights can still give an identity
  of the same shape, through linear relations between the products `G i * G (i + 1)`.
* `KTFib.mul_add_two_sub_succ_sq` (Cassini's identity):
  `G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2)`.
* `KTFib.mul_lucas`: `G (n + m) * L m = G (n + 2 * m) + (-t) ^ m * G n`.
* `KTFib.add_add_one_eq_mul_fib_add`: `G (m + n + 1) = G (m + 1) * F (n + 1) + t * G m * F n`.
* `KTFib.sum_pow_mul_lucas_sq`, `KTFib.sum_pow_mul_fib_sq`,
  `KTFib.sum_pow_mul_lucas_mul_lucas_succ`, `KTFib.sum_fib`, `KTFib.sum_lucas`, ...: closed forms
  over a field. The sums of `L i ^ 2`, `F i ^ 2`, `F (2 * i - 1)` and `L (2 * i)` assume `k ≠ 0`,
  the unweighted sums `KTFib.sum_fib` and `KTFib.sum_lucas` assume `k + t ≠ 1`, and the sums of
  `F (2 * i)`, `L (2 * i - 1)` and `L i * L (i + 1)` hold for every `k` (the last one needs
  `2 ≠ 0`).
* `KTFib.sum_lucas_sq`: for `k ^ 2 ≠ (t - 1) ^ 2`, the unweighted sum
  `∑ i ∈ Icc 1 n, L i ^ 2 = (L (2 * n + 2) - t ^ 2 * L (2 * n) - L 2 + 2 * t ^ 2) /
  (k ^ 2 - (t - 1) ^ 2) + 2 * ∑ i ∈ Icc 1 n, (-t) ^ i`, from `KTFib.lucas_sq` and the recurrence
  `KTFib.two_mul_add_two` of the even-indexed terms; `KTFib.sq_sub_sq_mul_sum_Icc_lucas_sq` is the
  division-free form.
* `KTFib.lucas_strictMonoOn`, `KTFib.lucas_monotoneOn`,
  `KTFib.lucas_mul_lucas_succ_monotoneOn`: for `1 ≤ k` and `0 ≤ t`, monotonicity from index `1`
  on (strict for `0 < t`), and `KTFib.lucas_mem_Icc`, `KTFib.lucas_mul_lucas_succ_mem_Icc`: for
  `1 ≤ k`, `0 ≤ t` and `1 ≤ i ≤ n`, the values at `i` lie between those at `1` and at `n`.
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
theorem Finset.sum_Icc_succ_top_pow_sub_mul {R : Type*} [Semiring R] (t : R) (f : ℕ → R)
    {a n : ℕ} (ha : a ≤ n + 1) :
    ∑ i ∈ Icc a (n + 1), t ^ (n + 1 - i) * f i =
      t * ∑ i ∈ Icc a n, t ^ (n - i) * f i + f (n + 1) := by
  rw [sum_Icc_succ_top ha, mul_sum, Nat.sub_self, pow_zero, one_mul]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  rw [Nat.sub_add_comm (mem_Icc.1 hi).2, pow_succ', mul_assoc]

namespace KTFib

/-! ### Subtraction-free identities -/

/-- For `k = 0`, a solution `F` of `F (n + 2) = k * F (n + 1) + t * F n` with `F 0 = 0`
vanishes at every even index: `F (2 * m) = 0`. -/
theorem fib_two_mul_eq_zero {R : Type*} [NonAssocSemiring R] {k t : R} {F : ℕ → R} (hk : k = 0)
    (hF0 : F 0 = 0) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (m : ℕ) : F (2 * m) = 0 := by
  subst hk
  induction m with
  | zero => exact hF0
  | succ m ih => rw [Nat.mul_succ, hF, ih, zero_mul, mul_zero, add_zero]

section CommSemiring

variable {R : Type*} [CommSemiring R] {k t : R} {G F L : ℕ → R}

/-- The `(k, t)`-Lucas sequence in terms of the `(k, t)`-Fibonacci sequence:
`L (n + 1) = F (n + 2) + t * F n`. -/
theorem lucas_add_one_eq_fib_add_two_add_mul_fib (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    L (n + 1) = F (n + 2) + t * F n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [hL1, hF, hF0, hF1]; ring
  | one => simp only [hL, hF, hL0, hL1, hF0, hF1]; ring
  | more n ih1 ih2 => rw [hL (n + 1), ih2, ih1, hF (n + 2), hF (n + 1), hF n]; ring

/-- The addition formula for a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`, in terms of
the `(k, t)`-Fibonacci sequence `F`: `G (m + n + 1) = G (m + 1) * F (n + 1) + t * G m * F n`.
For `G = F` this is `F (m + n + 1) = F (m + 1) * F (n + 1) + t * F m * F n`. -/
theorem add_add_one_eq_mul_fib_add (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + t * F n) (m n : ℕ) :
    G (m + n + 1) = G (m + 1) * F (n + 1) + t * G m * F n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hF0, hF1]
  | one => simp only [hF, hF0, hF1, hG]; ring
  | more n ih1 ih2 =>
    rw [show m + (n + 2) + 1 = m + n + 1 + 2 by omega, hG,
      show m + n + 1 + 1 = m + (n + 1) + 1 by omega, ih2, ih1, hF (n + 1), hF n]
    ring

end CommSemiring

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

/-- **The telescoping weights**: for weights `c i` and constants `a`, `b`,
`∑ i ∈ Icc 1 n, c i * (P i - t * P (i - 1)) = a * P n + b * P 0` holds for **every** sequence `P`
if and only if `c i = a * t ^ (n - i)` for `1 ≤ i ≤ n` and `b = -(a * t ^ n)`. With
`P i = G i * G (i + 1)` for a solution `G` of the recurrence, `k * G i ^ 2 = P i - t * P (i - 1)`,
so up to a constant factor `t ^ (n - i)` is the only weight for which the sum in
`KTFib.mul_sum_Icc_pow_mul_sq` telescopes term by term. -/
theorem forall_sum_Icc_mul_sub_mul_eq_iff {c : ℕ → R} {a b : R} {n : ℕ} :
    (∀ P : ℕ → R, ∑ i ∈ Icc 1 n, c i * (P i - t * P (i - 1)) = a * P n + b * P 0) ↔
      (∀ i ∈ Icc 1 n, c i = a * t ^ (n - i)) ∧ b = -(a * t ^ n) := by
  constructor
  · intro h
    -- test against the indicator sequences of single indices `j`
    have key (j : ℕ) := h fun m ↦ if m = j then 1 else 0
    have hsum (j : ℕ) : ∑ i ∈ Icc 1 n, c i * ((if i = j then (1 : R) else 0) -
        t * if i - 1 = j then 1 else 0) =
        (if j ∈ Icc 1 n then c j else 0) - t * if j + 1 ∈ Icc 1 n then c (j + 1) else 0 := by
      rw [sum_congr rfl fun i hi ↦ show c i * ((if i = j then (1 : R) else 0) -
          t * if i - 1 = j then 1 else 0) = (if i = j then c i else 0) -
          t * (if i = j + 1 then c i else 0) by
        have := (mem_Icc.1 hi).1
        split_ifs <;> first | ring1 | (exfalso; omega)]
      rw [sum_sub_distrib, ← mul_sum, sum_ite_eq', sum_ite_eq']
    simp only [hsum, mem_Icc] at key
    have hstep : ∀ j, 1 ≤ j → j < n → c j = t * c (j + 1) := fun j hj hjn ↦ by
      have := key j
      rw [ite_eq_left ⟨hj, hjn.le⟩, ite_eq_left ⟨by omega, hjn⟩, ite_eq_right (by omega),
        ite_eq_right (by omega)] at this
      linear_combination this
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · have := key 0
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl] at this
      exact ⟨fun i hi ↦ absurd (mem_Icc.1 hi) (by omega), by linear_combination -this⟩
    have hcn : c n = a := by
      have := key n
      rw [ite_eq_left ⟨hn, le_rfl⟩, ite_eq_right (by omega), ite_eq_left rfl,
        ite_eq_right (by omega)] at this
      linear_combination this
    have hc : ∀ m, m < n → c (n - m) = a * t ^ m := by
      intro m
      induction m with
      | zero => simp [hcn]
      | succ m ih =>
        intro hm
        rw [hstep (n - (m + 1)) (by omega) (by omega), show n - (m + 1) + 1 = n - m by omega,
          ih (by omega)]
        ring
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have hi' := mem_Icc.1 hi
      have := hc (n - i) (by omega)
      rwa [show n - (n - i) = i by omega] at this
    · have h0 := key 0
      rw [ite_eq_right (by omega), ite_eq_left ⟨le_rfl, hn⟩, ite_eq_right (by omega),
        ite_eq_left rfl] at h0
      have h1 := hc (n - 1) (by omega)
      rw [show n - (n - 1) = 1 by omega] at h1
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
      simp only [zero_add, Nat.add_sub_cancel] at h1
      linear_combination -h0 - t * h1
  · rintro ⟨hc, rfl⟩ P
    have key (m : ℕ) :
        ∑ i ∈ Icc 1 m, t ^ (m - i) * (P i - t * P (i - 1)) = P m - t ^ m * P 0 := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_Icc_succ_top_pow_sub_mul t _ (by omega), ih, Nat.add_sub_cancel]
        ring
    rw [sum_congr rfl fun i hi ↦ by rw [hc i hi, mul_assoc], ← mul_sum, key]
    ring

/-- Weights other than `t ^ (n - i)` can still give an identity of the shape of
`KTFib.mul_sum_Icc_pow_mul_sq`, through linear relations between the products `G i * G (i + 1)`:
for `n = 3` and the weights `c 1 = -(t * (2 * k ^ 2 + t))`, `c 2 = -k ^ 2`, `c 3 = 1`, every
solution `G` of `G (n + 2) = k * G (n + 1) + t * G n` satisfies
`k * ∑ i ∈ Icc 1 3, c i * G i ^ 2 = 2 * k ^ 2 * t ^ 2 * (G 0 * G 1)`. These weights are
proportional to `t ^ (3 - i)` only if `t = -k ^ 2`. -/
theorem mul_sum_Icc_one_three_mul_sq (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n)
    {c : ℕ → R} (hc1 : c 1 = -(t * (2 * k ^ 2 + t))) (hc2 : c 2 = -k ^ 2) (hc3 : c 3 = 1) :
    k * ∑ i ∈ Icc 1 3, c i * G i ^ 2 = 2 * k ^ 2 * t ^ 2 * (G 0 * G 1) := by
  have h0 := hG 0
  have h1 := hG 1
  simp only [zero_add] at h0 h1
  rw [show Icc 1 3 = {1, 2, 3} by rfl, sum_insert (by decide), sum_pair (by decide), hc1, hc2,
    hc3, h1, h0]
  ring

/-- **Cassini's identity** for a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n`:
`G i * G (i + 2) - G (i + 1) ^ 2 = (-t) ^ i * (G 0 * G 2 - G 1 ^ 2)`. -/
theorem mul_add_two_sub_succ_sq (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (i : ℕ) :
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
    have hC := mul_add_two_sub_succ_sq hG n
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


/-- The even-indexed terms of a solution `G` of `G (n + 2) = k * G (n + 1) + t * G n` solve the
`(k ^ 2 + 2 * t, -t ^ 2)`-recurrence:
`G (2 * (n + 2)) = (k ^ 2 + 2 * t) * G (2 * (n + 1)) + -t ^ 2 * G (2 * n)`. -/
theorem two_mul_add_two (hG : ∀ n, G (n + 2) = k * G (n + 1) + t * G n) (n : ℕ) :
    G (2 * (n + 2)) = (k ^ 2 + 2 * t) * G (2 * (n + 1)) + -t ^ 2 * G (2 * n) := by
  linear_combination (norm := ring_nf) hG (2 * n + 2) + k * hG (2 * n + 1) - t * hG (2 * n)

/-- The unweighted sum of squares of the `(k, t)`-Lucas numbers, in division-free form:
`(k ^ 2 - (t - 1) ^ 2) * ∑ i ∈ Icc 1 n, L i ^ 2 =
L (2 * n + 2) - t ^ 2 * L (2 * n) - L 2 + 2 * t ^ 2 +
2 * (k ^ 2 - (t - 1) ^ 2) * ∑ i ∈ Icc 1 n, (-t) ^ i`. -/
theorem sq_sub_sq_mul_sum_Icc_lucas_sq (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    (k ^ 2 - (t - 1) ^ 2) * ∑ i ∈ Icc 1 n, L i ^ 2 =
      L (2 * n + 2) - t ^ 2 * L (2 * n) - L 2 + 2 * t ^ 2 +
        2 * (k ^ 2 - (t - 1) ^ 2) * ∑ i ∈ Icc 1 n, (-t) ^ i := by
  have h := add_sub_one_mul_sum_Icc (G := fun i ↦ L (2 * i)) (two_mul_add_two hL) n
  simp only [mul_add, mul_one, mul_zero] at h
  rw [sum_congr rfl fun i _ ↦ lucas_sq hL0 hL1 hL i, sum_add_distrib, ← mul_sum]
  linear_combination h + t ^ 2 * hL0

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

/-- For `2 ≠ 0`: `∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
(L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k`. For `k = 0`
both sides vanish. -/
theorem sum_pow_mul_lucas_mul_lucas_succ [NeZero (2 : K)] (hL0 : L 0 = 2)
    (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * (L i * L (i + 1)) =
      (L (n + 1) ^ 2 - t ^ n * k ^ 2 + t ^ n * (k ^ 2 + 4 * t) * ((-1) ^ n - 1) / 2) / k := by
  obtain hk | hk := eq_or_ne k 0
  · have h := fib_two_mul_eq_zero (F := fun n ↦ L (n + 1)) hk (hL1.trans hk) fun n ↦ hL (n + 1)
    rw [hk, div_zero]
    refine sum_eq_zero fun i _ ↦ ?_
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [h j, mul_zero, mul_zero]
    · rw [h j, zero_mul, mul_zero]
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

/-- For `k ^ 2 ≠ (t - 1) ^ 2`, the unweighted sum of squares of the `(k, t)`-Lucas numbers:
`∑ i ∈ Icc 1 n, L i ^ 2 = (L (2 * n + 2) - t ^ 2 * L (2 * n) - L 2 + 2 * t ^ 2) /
(k ^ 2 - (t - 1) ^ 2) + 2 * ∑ i ∈ Icc 1 n, (-t) ^ i`. -/
theorem sum_lucas_sq (hkt : k ^ 2 ≠ (t - 1) ^ 2) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i ^ 2 =
      (L (2 * n + 2) - t ^ 2 * L (2 * n) - L 2 + 2 * t ^ 2) / (k ^ 2 - (t - 1) ^ 2) +
        2 * ∑ i ∈ Icc 1 n, (-t) ^ i := by
  have hkt' : k ^ 2 - (t - 1) ^ 2 ≠ 0 := sub_ne_zero.2 hkt
  rw [div_add' _ _ _ hkt', eq_div_iff hkt', mul_comm, sq_sub_sq_mul_sum_Icc_lucas_sq hL0 hL1 hL]
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
  obtain hk | hk := eq_or_ne k 0
  · simp [fib_two_mul_eq_zero hk hF0 hF, hk]
  rw [eq_div_iff hk, mul_comm, mul_sum_Icc_pow_mul_two_mul hF, hF1]
  ring

/-- `∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k`. For `k = 0` both
sides vanish. -/
theorem sum_pow_mul_lucas_two_mul_sub_one (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + t * L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, t ^ (n - i) * L (2 * i - 1) = (L (2 * n) - 2 * t ^ n) / k := by
  obtain hk | hk := eq_or_ne k 0
  · have h := fib_two_mul_eq_zero (F := fun n ↦ L (n + 1)) hk (hL1.trans hk) fun n ↦ hL (n + 1)
    rw [hk, div_zero]
    refine sum_eq_zero fun i hi ↦ ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (mem_Icc.1 hi).1
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, h j, mul_zero]
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
