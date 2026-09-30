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

/-- The `k`-recurrence is the `(k, 1)`-recurrence. -/
private lemma rec_one {G : ℕ → ℝ} (hG : ∀ n, G (n + 2) = k * G (n + 1) + G n) (n : ℕ) :
    G (n + 2) = k * G (n + 1) + 1 * G n := by
  rw [hG n, one_mul]

/-- At `t = 1` the total weight is `n`. -/
private lemma sum_one (n : ℕ) : ∑ _i ∈ Icc 1 n, (1 : ℝ) = n := by
  simp

/-- `1 / n ^ (α / 2 - 1) = n ^ (1 - α / 2)`. -/
private lemma one_div_rpow (n : ℕ) (α : ℝ) :
    (n : ℝ) ^ (1 - α / 2) = 1 / (n : ℝ) ^ (α / 2 - 1) := by
  rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n), neg_sub]

/-! ### Theorem 1.1 and Lemmas 2.2–2.4 -/

/-- Batte–Kaggwa, Theorem 1.1, first identity: `∑ L i ^ 2 = D_k(n)`. -/
theorem sum_sq_lucas (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i ^ 2 = (L n * L (n + 1) - 2 * k) / k := by
  have h := KTFib.sum_sq_lucas hk hL0 hL1 (rec_one hL) n
  simpa only [one_pow, one_mul, mul_one] using h

/-- Batte–Kaggwa, Theorem 1.1, second identity: `∑ F i ^ 2 = F n * F (n + 1) / k`. -/
theorem sum_sq_fib (hk : k ≠ 0) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, F i ^ 2 = F n * F (n + 1) / k := by
  have h := KTFib.sum_sq_fib hk hF0 hF1 (rec_one hF) n
  simpa only [one_pow, one_mul] using h

/-- Batte–Kaggwa, Theorem 1.1, third identity: `∑ L i * L (i + 1) = P_k(n)`. -/
theorem sum_lucas_mul_succ (hk : k ≠ 0) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (n : ℕ) :
    ∑ i ∈ Icc 1 n, L i * L (i + 1) =
      L (n + 1) ^ 2 / k - k + ((-1) ^ n - 1) * (2 / k + k / 2) := by
  have h := KTFib.sum_lucas_mul_succ hk hL0 hL1 (rec_one hL) n
  simp only [one_pow, one_mul] at h
  rw [h]
  field_simp
  ring

/-- Batte–Kaggwa, Theorem 1.1, fourth identity: `F i * L i = F (2 * i)`. -/
theorem fib_mul_lucas (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
    (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) (i : ℕ) :
    F i * L i = F (2 * i) := by
  exact KTFib.fib_mul_lucas hF0 hF1 (rec_one hF) hL0 hL1 (rec_one hL) i

/-- Batte–Kaggwa, Lemma 2.2: `L m ^ 2 = L (2 * m) + 2 * (-1) ^ m`. -/
theorem lucas_sq (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
    (m : ℕ) : L m ^ 2 = L (2 * m) + 2 * (-1) ^ m := by
  exact KTFib.lucas_sq hL0 hL1 (rec_one hL) m

/-- Batte–Kaggwa, Lemma 2.3: `L i * L (i + 1) = L (2 * i + 1) + k * (-1) ^ i`. -/
theorem lucas_mul_succ (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
    (i : ℕ) : L i * L (i + 1) = L (2 * i + 1) + k * (-1) ^ i := by
  exact KTFib.lucas_mul_succ hL0 hL1 (rec_one hL) i

/-- Batte–Kaggwa, Lemma 2.4: `L (i + 1) > L i` for `i ≥ 1`. -/
theorem lucas_lt_lucas_succ (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k)
    (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n) {i : ℕ} (hi : 1 ≤ i) : L i < L (i + 1) := by
  exact KTFib.lucas_lt_lucas_succ hk one_pos hL0 hL1 (rec_one hL) hi

/-! ### Theorem 1.2: the `k`-Lucas Hölder sandwich -/

section Sandwich

variable (hk : 1 ≤ k) (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
include hk hL0 hL1 hL

/-- Batte–Kaggwa, Theorem 1.2(i). -/
theorem holder_sandwich_i {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, L i ^ α ∧
      D ≤ 1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ∧
      (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) ≤ D := by
  have h := KTFib.holder_sandwich_of_one_lt_of_two_le hk le_rfl hL0 hL1 (rec_one hL) hn hp hpq hα
    h2α (D := D) (by rw [hD, one_pow, mul_one])
  simp only [one_pow, one_mul, sum_one, one_div_rpow] at h
  exact h

/-- Batte–Kaggwa, Theorem 1.2(ii). -/
theorem holder_sandwich_ii {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    ∑ i ∈ Icc 1 n, L i ^ α ≤
        (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ∧
      D ^ (α / 2) ≤ ∑ i ∈ Icc 1 n, L i ^ α := by
  have h := KTFib.holder_sandwich_of_one_lt_of_lt_two hk le_rfl hL0 hL1 (rec_one hL) hn hp hpq hα
    hα0 hα2 (D := D) (by rw [hD, one_pow, mul_one])
  simp only [one_pow, one_mul] at h
  exact h

/-- Batte–Kaggwa, Theorem 1.2(iii). -/
theorem holder_sandwich_iii {n : ℕ} {p q u v α D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (h2α : 2 ≤ α)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤ D ^ (α / 2) := by
  have h := KTFib.holder_sandwich_of_lt_one_of_two_le hk le_rfl hL0 hL1 (rec_one hL) hp0 hp1
    hpq hα h2α (D := D) (by rw [hD, one_pow, mul_one])
  simp only [one_pow, one_mul] at h
  exact h

/-- Batte–Kaggwa, Theorem 1.2(iv). -/
theorem holder_sandwich_iv {n : ℕ} (hn : 1 ≤ n) {p q u v α D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α) (hα2 : α < 2)
    (hD : D = (L n * L (n + 1) - 2 * k) / k) :
    (∑ i ∈ Icc 1 n, L i ^ u) ^ (1 / p) * (∑ i ∈ Icc 1 n, L i ^ v) ^ (1 / q) ≤
        ∑ i ∈ Icc 1 n, L i ^ α ∧
      ∑ i ∈ Icc 1 n, L i ^ α ≤ 1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ∧
      1 / (n : ℝ) ^ (α / 2 - 1) * D ^ (α / 2) ≤ D ∧
      D ≤ (∑ i ∈ Icc 1 n, L i ^ α) ^ (2 / α) := by
  have h := KTFib.holder_sandwich_of_lt_one_of_lt_two hk le_rfl hL0 hL1 (rec_one hL) hn hp0 hp1
    hpq hα hα0 hα2 (D := D) (by rw [hD, one_pow, mul_one])
  simp only [one_pow, one_mul, sum_one, one_div_rpow] at h
  exact h

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
  have h := KTFib.converse_holder_lucas_of_one_lt hk one_pos hL0 hL1 (rec_one hL) hn hp hpq hα huv
    hm hM (D := D) (by rw [hD, one_pow, mul_one])
  simp only [one_pow, one_mul] at h
  exact h

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
  have h := KTFib.converse_holder_lucas_of_lt_one hk one_pos hL0 hL1 (rec_one hL) hn hp0 hp1 hpq
    hα huv hm hM (D := D) (by rw [hD, one_pow, mul_one])
  simp only [one_pow, one_mul] at h
  exact h

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
    ∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ v +
        m₂ * M₂ / (M₁ * m₁) * ∑ i ∈ Icc 1 n, (L i * L (i + 1)) ^ u ≤
      (M₂ / m₁ + m₂ / M₁) * P := by
  have hk0 : k ≠ 0 := (zero_lt_one.trans_le hk).ne'
  have h := KTFib.cauchy_conversion_lucas hk one_pos hL0 hL1 (rec_one hL) hn huv hm₁ hM₁ hm₂
    hM₂ (P := P) (by rw [hP]; field_simp; ring)
  simp only [one_pow, one_mul, sum_one] at h
  exact h

end Converse

/-! ### Theorem 1.5, Theorem 4.1 and Corollary 4.1 -/

section CrossFamily

variable (hk : 0 < k) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hF : ∀ n, F (n + 2) = k * F (n + 1) + F n)
  (hL0 : L 0 = 2) (hL1 : L 1 = k) (hL : ∀ n, L (n + 2) = k * L (n + 1) + L n)
include hk hF0 hF1 hF hL0 hL1 hL

/-- Batte–Kaggwa, Theorem 1.5: `(∑ F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * D_k(n)`. -/
theorem sq_sum_fib_two_mul_le (n : ℕ) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  have h := KTFib.sq_sum_fib_two_mul_le hk one_pos hF0 hF1 (rec_one hF) hL0 hL1 (rec_one hL) n
  simpa only [one_pow, one_mul, mul_one] using h

/-- Batte–Kaggwa, Theorem 1.5, equality case: for `n ≥ 1`, equality holds iff `n = 1`. -/
theorem sq_sum_fib_two_mul_eq_iff {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Icc 1 n, F (2 * i)) ^ 2 = F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) ↔
      n = 1 := by
  have h := KTFib.sq_sum_fib_two_mul_eq_iff hk one_pos hF0 hF1 (rec_one hF) hL0 hL1 (rec_one hL) hn
  simpa only [one_pow, one_mul, mul_one] using h

/-- Batte–Kaggwa, Corollary 4.1: `((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * D_k(n)`. -/
theorem sq_fib_sub_one_div_le (n : ℕ) :
    ((F (2 * n + 1) - 1) / k) ^ 2 ≤ F n * F (n + 1) / k * ((L n * L (n + 1) - 2 * k) / k) := by
  have h := KTFib.sq_sum_fib_two_mul_le hk one_pos hF0 hF1 (rec_one hF) hL0 hL1 (rec_one hL) n
  rw [KTFib.sum_fib_even hk.ne' hF1 (rec_one hF)] at h
  simpa only [one_pow, one_mul, mul_one] using h

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
  have hk1 : k + 1 ≠ 1 := by simpa using hk
  have hk' : k + 1 - 1 = k := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [KTFib.sum_fib hk1 hF0 hF1 (rec_one hF), hk']
    ring
  · rw [KTFib.sum_lucas hk1 hL0 hL1 (rec_one hL), hk']
    ring
  · simpa only [one_pow, one_mul] using KTFib.sum_fib_odd hk hF0 (rec_one hF) n
  · simpa only [one_pow, one_mul] using KTFib.sum_fib_even hk hF1 (rec_one hF) n
  · simpa only [one_pow, one_mul, mul_one] using KTFib.sum_lucas_odd hk hL0 (rec_one hL) n
  · simpa only [one_pow, one_mul, mul_one] using KTFib.sum_lucas_even hk hL1 (rec_one hL) n

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
  have hF : ∀ n, (Nat.fib (n + 2) : ℝ) = 1 * Nat.fib (n + 1) + 1 * Nat.fib n := fun n => by
    rw [Nat.fib_add_two]; push_cast; ring
  have hL' : ∀ n, ((L (n + 2) : ℤ) : ℝ) =
      1 * ((L (n + 1) : ℤ) : ℝ) + 1 * ((L n : ℤ) : ℝ) :=
    fun n => by rw [hL]; push_cast; ring
  have hL0' : ((L 0 : ℤ) : ℝ) = 2 := by rw [hL0]; norm_num
  have hL1' : ((L 1 : ℤ) : ℝ) = 1 := by rw [hL1]; norm_num
  have hF0 : ((Nat.fib 0 : ℕ) : ℝ) = 0 := by simp
  have hF1 : ((Nat.fib 1 : ℕ) : ℝ) = 1 := by simp
  refine ⟨?_, fun hn => ?_⟩
  · have h := KTFib.sq_fib_sub_le (F := fun n => (Nat.fib n : ℝ))
      (L := fun n => ((L n : ℤ) : ℝ)) one_pos one_pos hF0 hF1 hF hL0' hL1' hL' n
    simp only [one_pow, mul_one] at h
    exact_mod_cast h
  · have h := KTFib.sq_fib_sub_eq_iff (F := fun n => (Nat.fib n : ℝ))
      (L := fun n => ((L n : ℤ) : ℝ)) one_pos one_pos hF0 hF1 hF hL0' hL1' hL' hn
    simp only [one_pow, mul_one] at h
    rw [← h]
    exact_mod_cast Iff.rfl

/-- The cross-family bound for the Jacobsthal numbers `J` and Jacobsthal–Lucas numbers `j`
(`(k, t) = (1, 2)`):
`(J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1))`,
with equality for `n ≥ 1` exactly when `n = 1`. -/
theorem Int.sq_jacobsthal_sub_le {J j : ℕ → ℤ} (hJ0 : J 0 = 0) (hJ1 : J 1 = 1)
    (hJ : ∀ n, J (n + 2) = J (n + 1) + 2 * J n) (hj0 : j 0 = 2) (hj1 : j 1 = 1)
    (hj : ∀ n, j (n + 2) = j (n + 1) + 2 * j n) (n : ℕ) :
    (J (2 * n + 1) - 2 ^ n) ^ 2 ≤ J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ∧
      (1 ≤ n → ((J (2 * n + 1) - 2 ^ n) ^ 2 = J n * J (n + 1) * (j n * j (n + 1) - 2 ^ (n + 1)) ↔
        n = 1)) := by
  have hJ' : ∀ n, ((J (n + 2) : ℤ) : ℝ) =
      1 * ((J (n + 1) : ℤ) : ℝ) + 2 * ((J n : ℤ) : ℝ) :=
    fun n => by rw [hJ]; push_cast; ring
  have hj' : ∀ n, ((j (n + 2) : ℤ) : ℝ) =
      1 * ((j (n + 1) : ℤ) : ℝ) + 2 * ((j n : ℤ) : ℝ) :=
    fun n => by rw [hj]; push_cast; ring
  have hJ0' : ((J 0 : ℤ) : ℝ) = 0 := by rw [hJ0]; norm_num
  have hJ1' : ((J 1 : ℤ) : ℝ) = 1 := by rw [hJ1]; norm_num
  have hj0' : ((j 0 : ℤ) : ℝ) = 2 := by rw [hj0]; norm_num
  have hj1' : ((j 1 : ℤ) : ℝ) = 1 := by rw [hj1]; norm_num
  have h2 : (2 : ℝ) * 1 * 2 ^ n = 2 ^ (n + 1) := by ring
  refine ⟨?_, fun hn => ?_⟩
  · have h := KTFib.sq_fib_sub_le (F := fun n => ((J n : ℤ) : ℝ))
      (L := fun n => ((j n : ℤ) : ℝ)) one_pos two_pos hJ0' hJ1' hJ' hj0' hj1' hj' n
    rw [h2] at h
    exact_mod_cast h
  · have h := KTFib.sq_fib_sub_eq_iff (F := fun n => ((J n : ℤ) : ℝ))
      (L := fun n => ((j n : ℤ) : ℝ)) one_pos two_pos hJ0' hJ1' hJ' hj0' hj1' hj' hn
    rw [h2] at h
    rw [← h]
    exact_mod_cast Iff.rfl
