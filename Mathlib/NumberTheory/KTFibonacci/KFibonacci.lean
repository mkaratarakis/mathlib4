/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.KTFibonacci.Holder
public import Mathlib.Data.Nat.Fib.Basic

/-!
# The `k`-Fibonacci and `k`-Lucas case: the results of Batte and Kaggwa

At `t = 1` the weights `t ^ (n - i)` are all `1`, and the results of
`Mathlib/NumberTheory/KTFibonacci/Holder.lean` become those of

> H. Batte and P. Kaggwa, *`k`-Fibonacci and `k`-Lucas numbers with the Hölder inequality*,
> arXiv:2609.33573.

Each declaration below is one of their results, named in its docstring, and is proved as a
corollary of the `(k, t)` version.  The paper takes `k` to be a positive integer; here `k` is
any real number `k ≥ 1` (or `k > 0` where that suffices).  Throughout,
`D = (L n * L (n + 1) - 2 * k) / k` is their `D_k(n)` and
`P = L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2)` is their `P_k(n)`.

At `k = 1` we also record their Corollary 5.1 for `Nat.fib` and the Lucas numbers, and, as an
instance with `t ≠ 1` that the `k`-Fibonacci setting cannot reach, the cross-family bound for
the Jacobsthal numbers (`(k, t) = (1, 2)`).
-/

@[expose] public section

open Finset

namespace KFib

variable {k : ℝ} {F L : ℕ → ℝ}

/-! ### Theorem 1.1 and Lemmas 2.2–2.4 -/

/-- Batte–Kaggwa, Theorem 1.1, first identity: `∑ L i ^ 2 = D_k(n)`. -/
theorem sum_sq_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i ^ 2 = (L n * L (n + 1) - 2 * k) / k := by
  sorry

/-- Batte–Kaggwa, Theorem 1.1, second identity: `∑ F i ^ 2 = F n * F (n + 1) / k`. -/
theorem sum_sq_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i ^ 2 = F n * F (n + 1) / k := by
  sorry

/-- Batte–Kaggwa, Theorem 1.1, third identity: `∑ L i * L (i + 1) = P_k(n)`. -/
theorem sum_lucas_mul_succ (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i * L (i + 1) =
      L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2) := by
  sorry

/-- Batte–Kaggwa, Theorem 1.1, fourth identity: `F i * L i = F (2 * i)`. -/
theorem fib_mul_lucas (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (i : ℕ) :
    F i * L i = F (2 * i) := by
  sorry

/-- Batte–Kaggwa, Lemma 2.2: `L m ^ 2 = L (2 * m) + 2 * (-1) ^ m`. -/
theorem lucas_sq (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
    (m : ℕ) : L m ^ 2 = L (2 * m) + 2 * (-1) ^ m := by
  sorry

/-- Batte–Kaggwa, Lemma 2.3: `L i * L (i + 1) = L (2 * i + 1) + k * (-1) ^ i`. -/
theorem lucas_mul_succ (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
    (i : ℕ) : L i * L (i + 1) = L (2 * i + 1) + k * (-1) ^ i := by
  sorry

/-- Batte–Kaggwa, Lemma 2.4: `L (i + 1) > L i` for `i ≥ 1`. -/
theorem lucas_lt_lucas_succ (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {i : ℕ} (hi : 1 ≤ i) : L i < L (i + 1) := by
  sorry

/-! ### Theorem 1.2: the `k`-Lucas Hölder sandwich -/

section Sandwich

variable (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
include hk hL0 hL1 hL

/-- Batte–Kaggwa, Theorem 1.2(i). -/
theorem holder_sandwich_i {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤ (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, L i ^ α ∧
      D ≤ 1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) ≤ D := by
  sorry

/-- Batte–Kaggwa, Theorem 1.2(ii). -/
theorem holder_sandwich_ii {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤ (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, L i ^ α := by
  sorry

/-- Batte–Kaggwa, Theorem 1.2(iii). -/
theorem holder_sandwich_iii {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤ ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤ D ^ (α / 2) := by
  sorry

/-- Batte–Kaggwa, Theorem 1.2(iv). -/
theorem holder_sandwich_iv {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤ ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤ 1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ≤ D ∧
      D ≤ (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) := by
  sorry

end Sandwich

/-! ### Theorems 1.3 and 1.4: converse Hölder and converse Cauchy refinements -/

section Converse

variable (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
include hk hL0 hL1 hL

/-- Batte–Kaggwa, Theorem 1.3, for `p > 1`. -/
theorem converse_holder_of_one_lt {n : ℕ} (hn : 2 ≤ n) {p q u v m M D : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    0 < m ∧ m < M ∧
      (M - m) * ∑ i ∈ Icc 1 n, L i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, L i ^ v ≤
        (M ^ p - m ^ p) * D ∧
      (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          D := by
  sorry

/-- Batte–Kaggwa, Theorem 1.3, for `0 < p < 1` ("both inequalities reverse"). -/
theorem converse_holder_of_lt_one {n : ℕ} (hn : 2 ≤ n) {p q u v m M D : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = 2) (huv : u ≠ v)
    (hm : m = min (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hM : M = max (L 1 ^ ((u - v) / p)) (L n ^ ((u - v) / p)))
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    0 < m ∧ m < M ∧
      (M ^ p - m ^ p) * D ≤
        (M - m) * ∑ i ∈ Icc 1 n, L i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ Icc 1 n, L i ^ v ∧
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
          D ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) := by
  sorry

/-- Batte–Kaggwa, Theorem 1.4, with `x i = L i * L (i + 1)` and `u + v = 2`.  The third
inequality is the one whose source (Ozeki's inequality) fails for general tuples
(`Real.not_ozeki`); it holds here by `Real.ozeki_rpow`. -/
theorem cauchy_conversion {n : ℕ} (hn : 1 ≤ n) {u v m₁ M₁ m₂ M₂ P : ℝ} (huv : u + v = 2)
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
    ∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v + m₂ * M₂ / (M₁ * m₁) * ∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u ≤
      (M₂ / m₁ + m₂ / M₁) * P := by
  sorry

end Converse

/-! ### Theorem 1.5, Theorem 4.1 and Corollary 4.1 -/

section CrossFamily

variable (hk : 0 < k) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
  (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
include hk hF0 hF1 hF hL0 hL1 hL

/-- Batte–Kaggwa, Theorem 1.5: `(∑ F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * D_k(n)`. -/
theorem sq_sum_fib_two_mul_le (n : ℕ) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  sorry

/-- Batte–Kaggwa, Theorem 1.5, equality case: for `n ≥ 1`, equality holds iff `n = 1`. -/
theorem sq_sum_fib_two_mul_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 = F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) ↔
      n = 1 := by
  sorry

/-- Batte–Kaggwa, Corollary 4.1: `((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * D_k(n)`. -/
theorem sq_fib_sub_one_div_le (n : ℕ) :
    ((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  sorry

end CrossFamily

/-- Batte–Kaggwa, Theorem 4.1, identities (4.1)–(4.6). -/
theorem sums (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i = (F n + F (n + 1) - 1) / k ∧
      ∑ i ∈ Icc 1 n, L i = (L n + L (n + 1) - k - 2) / k ∧
      ∑ i ∈ Icc 1 n, F (2 * i - 1) = F (2 * n) / k ∧
      ∑ i ∈ Icc 1 n, F (2 * i) = (F (2 * n + 1) - 1) / k ∧
      ∑ i ∈ Icc 1 n, L (2 * i - 1) = (L (2 * n) - 2) / k ∧
      ∑ i ∈ Icc 1 n, L (2 * i) = (L (2 * n + 1) - k) / k := by
  sorry

end KFib

/-! ### `k = 1`: Fibonacci and Lucas numbers, and the Jacobsthal instance -/

/-- Batte–Kaggwa, Corollary 5.1: for the Fibonacci numbers `Nat.fib` and the Lucas numbers
`L`, `(F (2 * n + 1) - 1) ^ 2 ≤ F n * F (n + 1) * (L n * L (n + 1) - 2)`, with equality for
`n ≥ 1` exactly when `n = 1`. -/
theorem Nat.sq_fib_sub_one_le {L : ℕ → ℤ} (hL0 : L 0 = 2) (hL1 : L 1 = 1)
    (hL : ∀ n, L (n + 2) = L (n + 1) + L n) (n : ℕ) :
    ((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 ≤
        Nat.fib n * Nat.fib (n + 1) * (L n * L (n + 1) - 2) ∧
      (1 ≤ n → (((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 =
        Nat.fib n * Nat.fib (n + 1) * (L n * L (n + 1) - 2) ↔ n = 1)) := by
  sorry

/-- The cross-family bound for the Jacobsthal numbers `J` and Jacobsthal–Lucas numbers `j`
(`(k, t) = (1, 2)`): `(J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1))`,
with equality for `n ≥ 1` exactly when `n = 1`. -/
theorem Int.sq_jacobsthal_sub_le {J j : ℕ → ℤ} (hJ0 : J 0 = 0) (hJ1 : J 1 = 1)
    (hJ : ∀ n, J (n + 2) = J (n + 1) + 2 * J n) (hj0 : j 0 = 2) (hj1 : j 1 = 1)
    (hj : ∀ n, j (n + 2) = j (n + 1) + 2 * j n) (n : ℕ) :
    (J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ∧
      (1 ≤ n → ((J (2 * n + 1) - 2 ^ n) ^ 2 = J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ↔
        n = 1)) := by
  sorry
