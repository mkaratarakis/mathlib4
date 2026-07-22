/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Fib.Basic

/-!
# A `k`-Fibonacci annulus for the zeros of a polynomial

This file formalises the two main results of

> S. Kaur, *k-Fibonacci annulus for polynomial zeros*.

The `k`-Fibonacci sequence is **not** introduced as a new definition: every statement takes an
arbitrary sequence `F : ℕ → ℝ` together with the hypotheses `F 0 = 0`, `F 1 = 1` and
`F (n + 2) = k * F (n + 1) + F n` as explicit assumptions.  Specialising `F` to
`fun n ↦ (Nat.fib n : ℝ)` and `k` to `1` recovers the classical Fibonacci statements.

## Main results

* `Real.sum_choose_mul_kFib` (**Theorem 1.1**): for any such `F`,
  `∑ ℓ ≤ n, n.choose ℓ * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ = F ((m + 1) * n)`
  (with `m` shifted by one relative to the paper so that all indices are naturals).
* `Polynomial.norm_le_of_isRoot_of_sum_weights`, `Polynomial.le_norm_of_isRoot_of_sum_weights`:
  the analytic core of Theorem 1.2, for an arbitrary weight sequence summing to `1`.
* `Polynomial.isRoot_mem_kFib_annulus` (**Theorem 1.2**): every zero of a polynomial over `ℂ`
  lies in the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with the paper's `k`-Fibonacci radii, stated via
  `Finset.inf'`/`Finset.sup'` and real `rpow`.
* `Polynomial.isRoot_mem_kFib_annulus_four` (**Corollary 1.3**, Bidkham–Shashahani): the case
  `m = 4` of the paper, with `F 3 = k ^ 2 + 1`, `F 4 = k ^ 3 + 2 * k`.
* `Polynomial.isRoot_mem_fib_annulus` (**Remark 1.4**, Diaz-Barrero): the classical case
  `k = 1`, phrased with `Nat.fib`.

## Implementation notes

The proof of the summation identity avoids the Binet formula quoted in the paper.  Writing
`α, β` for the roots of `X ^ 2 - k * X - 1`, the single induction
`α ^ (j + 1) = F (j + 1) * α + F j` gives both `α ^ (m + 1) = F m + F (m + 1) * α` — so the sum
is a binomial expansion of `(α ^ (m + 1)) ^ n` — and the Binet formula
`F j * (α - β) = α ^ j - β ^ j` as a byproduct.

The lower bound of Theorem 1.2 is proved directly on the constant coefficient rather than via
the reversed polynomial `zⁿ q(1/z)` used in the paper; this avoids any detour through
`Polynomial.reverse`.
-/

@[expose] public section

open Finset

namespace Real

variable {k : ℝ} {F : ℕ → ℝ}

section Recurrence

variable (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ n, F (n + 2) = k * F (n + 1) + F n)
include hF0 hF1 hrec

/-- If `α ^ 2 = k * α + 1` then the powers of `α` are the linear forms `F (j + 1) * α + F j`. -/
theorem pow_succ_eq_of_sq_eq {α : ℝ} (hα : α ^ 2 = k * α + 1) (j : ℕ) :
    α ^ (j + 1) = F (j + 1) * α + F j := by
  induction j with
  | zero => simp [hF0, hF1]
  | succ j ih =>
    have : α ^ (j + 1 + 1) = α * α ^ (j + 1) := by ring
    rw [this, ih, hrec j]
    linear_combination F (j + 1) * hα

/-- The Binet formula, in the form that avoids dividing by `α - β`.  It is an immediate
consequence of `Real.pow_succ_eq_of_sq_eq` applied to both roots. -/
theorem mul_sub_eq_pow_sub_pow {α β : ℝ} (hα : α ^ 2 = k * α + 1) (hβ : β ^ 2 = k * β + 1)
    (j : ℕ) : F j * (α - β) = α ^ j - β ^ j := by
  cases j with
  | zero => simp [hF0]
  | succ i =>
    rw [pow_succ_eq_of_sq_eq hF0 hF1 hrec hα i, pow_succ_eq_of_sq_eq hF0 hF1 hrec hβ i]
    ring

/-- **Theorem 1.1** of the paper, stated for the two roots `α ≠ β` of `X ^ 2 - k * X - 1`.
The index `m` of the paper is shifted by one so that all indices are natural numbers. -/
theorem sum_choose_mul_of_sq_eq {α β : ℝ} (hα : α ^ 2 = k * α + 1)
    (hβ : β ^ 2 = k * β + 1) (hne : α ≠ β) (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ
      = F ((m + 1) * n) := by
  have hd : α - β ≠ 0 := sub_ne_zero.2 hne
  have hbinet := mul_sub_eq_pow_sub_pow hF0 hF1 hrec hα hβ
  have hA : F (m + 1) * α + F m = α ^ (m + 1) :=
    (pow_succ_eq_of_sq_eq hF0 hF1 hrec hα m).symm
  have hB : F (m + 1) * β + F m = β ^ (m + 1) :=
    (pow_succ_eq_of_sq_eq hF0 hF1 hrec hβ m).symm
  refine mul_right_cancel₀ hd ?_
  have step :
      (∑ ℓ ∈ range (n + 1), (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ) * (α - β)
        = (∑ ℓ ∈ range (n + 1), (F (m + 1) * α) ^ ℓ * F m ^ (n - ℓ) * (n.choose ℓ : ℝ))
          - ∑ ℓ ∈ range (n + 1), (F (m + 1) * β) ^ ℓ * F m ^ (n - ℓ) * (n.choose ℓ : ℝ) := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [mul_pow, mul_pow]
    linear_combination (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * hbinet ℓ
  rw [step, ← add_pow, ← add_pow, hA, hB, ← pow_mul, ← pow_mul, hbinet ((m + 1) * n)]

/-- **Theorem 1.1** of the paper.  For any sequence `F` satisfying the `k`-Fibonacci recurrence
`F (n + 2) = k * F (n + 1) + F n` with `F 0 = 0` and `F 1 = 1`,
`∑ ℓ ≤ n, (n.choose ℓ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ = F ((m + 1) * n)`.

Note that no positivity assumption on `k` is needed. -/
theorem sum_choose_mul_kFib (m n : ℕ) :
    ∑ ℓ ∈ range (n + 1), (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ
      = F ((m + 1) * n) := by
  have hnn : (0 : ℝ) ≤ k ^ 2 + 4 := by positivity
  have hs2 : Real.sqrt (k ^ 2 + 4) ^ 2 = k ^ 2 + 4 := Real.sq_sqrt hnn
  have hspos : 0 < Real.sqrt (k ^ 2 + 4) := Real.sqrt_pos.2 (by positivity)
  refine sum_choose_mul_of_sq_eq hF0 hF1 hrec (α := (k + Real.sqrt (k ^ 2 + 4)) / 2)
    (β := (k - Real.sqrt (k ^ 2 + 4)) / 2) ?_ ?_ ?_ m n
  · linear_combination hs2 / 4
  · linear_combination hs2 / 4
  · intro h
    rw [div_eq_div_iff (by norm_num) (by norm_num)] at h
    linarith

/-- For positive `k`, a `k`-Fibonacci sequence is nonnegative, and strictly positive from
index `1` onwards. -/
theorem kFib_nonneg_and_pos (hk : 0 < k) (j : ℕ) : 0 ≤ F j ∧ 0 < F (j + 1) := by
  induction j with
  | zero => exact ⟨hF0.ge, by rw [hF1]; norm_num⟩
  | succ j ih =>
    refine ⟨ih.2.le, ?_⟩
    rw [hrec j]
    nlinarith [ih.1, ih.2]

theorem kFib_nonneg (hk : 0 < k) (j : ℕ) : 0 ≤ F j :=
  (kFib_nonneg_and_pos hF0 hF1 hrec hk j).1

theorem kFib_pos (hk : 0 < k) (j : ℕ) : 0 < F (j + 1) :=
  (kFib_nonneg_and_pos hF0 hF1 hrec hk j).2

theorem kFib_two : F 2 = k := by
  have := hrec 0; rw [hF0, hF1] at this; linarith

theorem kFib_three : F 3 = k ^ 2 + 1 := by
  have h2 := kFib_two hF0 hF1 hrec
  have := hrec 1; rw [hF1, h2] at this; nlinarith

theorem kFib_four : F 4 = k ^ 3 + 2 * k := by
  have h2 := kFib_two hF0 hF1 hrec
  have h3 := kFib_three hF0 hF1 hrec
  have := hrec 2; rw [h2, h3] at this; nlinarith

end Recurrence

end Real

namespace Polynomial

open Finset

/-- The analytic core of Theorem 1.2: if the weights `A ℓ` are nonnegative, sum to `1` over
`1 ≤ ℓ ≤ n`, and dominate the coefficient ratios `‖a (n - ℓ)‖ / ‖a n‖` at scale `R`, then
every root of `p` has norm at most `R`.

This is stated for an arbitrary weight sequence `A`; Theorem 1.1 supplies the `k`-Fibonacci
weights `A ℓ = (n.choose ℓ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ / F ((m + 1) * n)`. -/
theorem norm_le_of_isRoot_of_sum_weights {p : ℂ[X]} {A : ℕ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ ℓ, 0 ≤ A ℓ) (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff (p.natDegree - ℓ)‖ ≤ A ℓ * ‖p.leadingCoeff‖ * R ^ ℓ)
    {z : ℂ} (hz : p.IsRoot z) : ‖z‖ ≤ R := by
  set n := p.natDegree with hn
  by_contra hcon
  push Not at hcon
  have hz0 : 0 < ‖z‖ := hR.trans_lt hcon
  -- The weights sum to `1`, so `Icc 1 n` is nonempty and hence `p ≠ 0`.
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hn1
    exact absurd hn1 (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  -- Some weight is strictly positive, since the weights sum to `1`.
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ Icc 1 n, 0 < A j := by
    by_contra hall
    push Not at hall
    have : ∑ ℓ ∈ Icc 1 n, A ℓ = 0 :=
      sum_eq_zero fun ℓ hℓ => le_antisymm (hall ℓ hℓ) (hA ℓ)
    rw [hsum] at this
    exact one_ne_zero this
  -- Split the leading term off the evaluation of `p` at `z`.
  have heval : p.leadingCoeff * z ^ n = -∑ i ∈ range n, p.coeff i * z ^ i := by
    have := hz
    rw [IsRoot.def, eval_eq_sum_range, ← hn, range_add_one, sum_insert (by simp)] at this
    rw [← coeff_natDegree, ← hn, eq_neg_iff_add_eq_zero]
    exact this
  -- Reindex `range n` as `Icc 1 n` via `i ↦ n - i`.
  have hreindex : ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i
      = ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ) := by
    refine sum_nbij' (fun i => n - i) (fun ℓ => n - ℓ) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_range] at hi
      simp only [mem_Icc]
      omega
    · intro ℓ hℓ
      simp only [mem_Icc] at hℓ
      simp only [mem_range]
      omega
    · intro i hi
      simp only [mem_range] at hi
      omega
    · intro ℓ hℓ
      simp only [mem_Icc] at hℓ
      omega
    · intro i hi
      simp only [mem_range] at hi
      rw [Nat.sub_sub_self hi.le]
  -- The tail is strictly dominated by the leading term.
  have hkey : ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ)
      < ‖p.leadingCoeff‖ * ‖z‖ ^ n := by
    have hlt : ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ)
        < ∑ ℓ ∈ Icc 1 n,
            A ℓ * ‖p.leadingCoeff‖ * ‖z‖ ^ ℓ * ‖z‖ ^ (n - ℓ) := by
      refine sum_lt_sum (fun ℓ hℓ => ?_) ⟨j, hj, ?_⟩
      · have h1 := hcoeff ℓ hℓ
        have h2 : R ^ ℓ ≤ ‖z‖ ^ ℓ := pow_le_pow_left₀ hR hcon.le ℓ
        have h3 : A ℓ * ‖p.leadingCoeff‖ * R ^ ℓ
            ≤ A ℓ * ‖p.leadingCoeff‖ * ‖z‖ ^ ℓ :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (hA ℓ) (norm_nonneg _))
        nlinarith [pow_pos hz0 (n - ℓ), norm_nonneg (p.coeff (n - ℓ))]
      · have h1 := hcoeff j hj
        have h2 : R ^ j < ‖z‖ ^ j := by
          refine pow_lt_pow_left₀ hcon hR ?_
          simp only [mem_Icc] at hj
          omega
        have h3 : A j * ‖p.leadingCoeff‖ * R ^ j < A j * ‖p.leadingCoeff‖ * ‖z‖ ^ j :=
          mul_lt_mul_of_pos_left h2 (by positivity)
        nlinarith [pow_pos hz0 (n - j)]
    refine hlt.trans_le (le_of_eq ?_)
    have hrw :
        ∑ ℓ ∈ Icc 1 n, A ℓ * ‖p.leadingCoeff‖ * ‖z‖ ^ ℓ * ‖z‖ ^ (n - ℓ)
          = ∑ ℓ ∈ Icc 1 n, A ℓ * (‖p.leadingCoeff‖ * ‖z‖ ^ n) := by
      refine sum_congr rfl fun ℓ hℓ => ?_
      simp only [mem_Icc] at hℓ
      rw [mul_assoc, mul_assoc, ← pow_add, Nat.add_sub_cancel' hℓ.2]
    rw [hrw, ← sum_mul, hsum, one_mul]
  -- Contradiction.
  have : ‖p.leadingCoeff‖ * ‖z‖ ^ n < ‖p.leadingCoeff‖ * ‖z‖ ^ n := by
    calc ‖p.leadingCoeff‖ * ‖z‖ ^ n = ‖p.leadingCoeff * z ^ n‖ := by
          rw [norm_mul, norm_pow]
      _ = ‖∑ i ∈ range n, p.coeff i * z ^ i‖ := by rw [heval, norm_neg]
      _ ≤ ∑ i ∈ range n, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ range n, ‖p.coeff i‖ * ‖z‖ ^ i := by
          refine sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_pow]
      _ = ∑ ℓ ∈ Icc 1 n, ‖p.coeff (n - ℓ)‖ * ‖z‖ ^ (n - ℓ) := hreindex
      _ < ‖p.leadingCoeff‖ * ‖z‖ ^ n := hkey
  exact absurd this (lt_irrefl _)

/-- **Theorem 1.2** of the paper (upper bound), with the `k`-Fibonacci weights supplied by
`Real.sum_choose_mul_kFib`.  If `R ≥ 0` dominates every coefficient ratio in the sense that
`‖a (n - ℓ)‖ * F ((m + 1) * n)` is at most
`(n.choose ℓ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ * (‖a n‖ * R ^ ℓ)` for `1 ≤ ℓ ≤ n`, then
every zero of `p` lies in the closed disc of radius `R`.

The paper's `r₂` (see `Polynomial.norm_le_kFib_sup_of_isRoot`) is exactly the least such
`R`. -/
theorem norm_le_of_isRoot_kFib {p : ℂ[X]} {k : ℝ} {F : ℕ → ℝ} (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    (m : ℕ) (hdeg : 1 ≤ p.natDegree) {R : ℝ} (hR : 0 ≤ R)
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff (p.natDegree - ℓ)‖ * F ((m + 1) * p.natDegree)
        ≤ (p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            * (‖p.leadingCoeff‖ * R ^ ℓ))
    {z : ℂ} (hz : p.IsRoot z) : ‖z‖ ≤ R := by
  set n := p.natDegree with hn
  have hFnn := Real.kFib_nonneg hF0 hF1 hrec hk
  -- `F ((m + 1) * n)` is positive, since `(m + 1) * n ≥ 1`.
  obtain ⟨t, ht⟩ : ∃ t, (m + 1) * n = t + 1 := ⟨(m + 1) * n - 1, by
    have : 1 ≤ (m + 1) * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩
  have hD : 0 < F ((m + 1) * n) := by
    rw [ht]; exact Real.kFib_pos hF0 hF1 hrec hk t
  -- The numerators of the weights are nonnegative.
  have hNnn : ∀ ℓ, 0 ≤ (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ :=
    fun ℓ => mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (hFnn m) _)) (pow_nonneg (hFnn (m + 1)) _)) (hFnn ℓ)
  refine norm_le_of_isRoot_of_sum_weights
    (A := fun ℓ =>
      (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ / F ((m + 1) * n))
    hR (fun ℓ => div_nonneg (hNnn ℓ) hD.le) ?_ ?_ hz
  · -- The weights sum to `1`: the `ℓ = 0` term of Theorem 1.1 vanishes because `F 0 = 0`.
    have hthm := Real.sum_choose_mul_kFib hF0 hF1 hrec m n
    have hins : range (n + 1) = insert 0 (Icc 1 n) := by
      ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hins, sum_insert (by simp)] at hthm
    have hzero : (n.choose 0 : ℝ) * F m ^ (n - 0) * F (m + 1) ^ 0 * F 0 = 0 := by
      rw [hF0, mul_zero]
    rw [hzero, zero_add] at hthm
    rw [← sum_div, hthm, div_self hD.ne']
  · intro ℓ hℓ
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hD, mul_assoc]
    exact hcoeff ℓ hℓ

/-- The analytic core of the lower bound in Theorem 1.2: if the weights `A ℓ` are nonnegative,
sum to `1` over `1 ≤ ℓ ≤ n`, and `‖a ℓ‖ * r ^ ℓ ≤ A ℓ * ‖a 0‖` for all `1 ≤ ℓ ≤ n`, then
every root of `p` has norm at least `r`.

The paper deduces this from the upper bound applied to the reversed polynomial
`Q(z) = zⁿ q(1/z)`; here we simply run the same estimate directly on the constant term. -/
theorem le_norm_of_isRoot_of_sum_weights {p : ℂ[X]} {A : ℕ → ℝ} {r : ℝ}
    (hA : ∀ ℓ, 0 ≤ A ℓ) (hsum : ∑ ℓ ∈ Icc 1 p.natDegree, A ℓ = 1)
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff ℓ‖ * r ^ ℓ ≤ A ℓ * ‖p.coeff 0‖)
    {z : ℂ} (hz : p.IsRoot z) : r ≤ ‖z‖ := by
  set n := p.natDegree with hn
  by_contra hcon
  push Not at hcon
  have hr0 : 0 < r := (norm_nonneg z).trans_lt hcon
  -- The weights sum to `1`, so `Icc 1 n` is nonempty and hence `p ≠ 0`.
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hn1
    exact absurd hn1 (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  have hins : range (n + 1) = insert 0 (Icc 1 n) := by
    ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
  -- If the constant coefficient vanishes, the hypothesis at `ℓ = n` is already contradictory.
  rcases eq_or_ne (p.coeff 0) 0 with h0 | h0
  · have h := hcoeff n (mem_Icc.2 ⟨hn1, le_rfl⟩)
    rw [h0, norm_zero, mul_zero] at h
    simp only [hn, coeff_natDegree] at h
    exact absurd h (not_le.2 (mul_pos hlc (pow_pos hr0 _)))
  have h0' : 0 < ‖p.coeff 0‖ := norm_pos_iff.2 h0
  -- Some weight is strictly positive, since the weights sum to `1`.
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ Icc 1 n, 0 < A j := by
    by_contra hall
    push Not at hall
    have : ∑ ℓ ∈ Icc 1 n, A ℓ = 0 :=
      sum_eq_zero fun ℓ hℓ => le_antisymm (hall ℓ hℓ) (hA ℓ)
    rw [hsum] at this
    exact one_ne_zero this
  -- Isolate the constant term in the evaluation of `p` at `z`.
  have heval : p.coeff 0 = -∑ ℓ ∈ Icc 1 n, p.coeff ℓ * z ^ ℓ := by
    have h := hz
    rw [IsRoot.def, eval_eq_sum_range, ← hn, hins, sum_insert (by simp)] at h
    rw [pow_zero, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  -- The constant term is strictly dominated by the tail, a contradiction.
  have hbound : ‖p.coeff 0‖ < ∑ ℓ ∈ Icc 1 n, A ℓ * ‖p.coeff 0‖ := by
    calc ‖p.coeff 0‖
        = ‖∑ ℓ ∈ Icc 1 n, p.coeff ℓ * z ^ ℓ‖ := by rw [heval, norm_neg]
      _ ≤ ∑ ℓ ∈ Icc 1 n, ‖p.coeff ℓ * z ^ ℓ‖ := norm_sum_le _ _
      _ = ∑ ℓ ∈ Icc 1 n, ‖p.coeff ℓ‖ * ‖z‖ ^ ℓ := by
          refine sum_congr rfl fun ℓ _ => ?_
          rw [norm_mul, norm_pow]
      _ < ∑ ℓ ∈ Icc 1 n, A ℓ * ‖p.coeff 0‖ := ?_
    refine sum_lt_sum (fun ℓ hℓ => ?_) ⟨j, hj, ?_⟩
    · have h2 : ‖z‖ ^ ℓ ≤ r ^ ℓ := pow_le_pow_left₀ (norm_nonneg z) hcon.le ℓ
      have h1 := hcoeff ℓ hℓ
      nlinarith [norm_nonneg (p.coeff ℓ)]
    · have hj1 : j ≠ 0 := by simp only [mem_Icc] at hj; omega
      rcases eq_or_ne (p.coeff j) 0 with hcj | hcj
      · simpa [hcj] using mul_pos hjpos h0'
      · have h2 : ‖z‖ ^ j < r ^ j := pow_lt_pow_left₀ hcon (norm_nonneg z) hj1
        have h1 := hcoeff j hj
        have hcj' : 0 < ‖p.coeff j‖ := norm_pos_iff.2 hcj
        nlinarith
  rw [← sum_mul, hsum, one_mul] at hbound
  exact absurd hbound (lt_irrefl _)

/-- **Theorem 1.2** of the paper (lower bound), with the `k`-Fibonacci weights supplied by
`Real.sum_choose_mul_kFib`: if `‖a ℓ‖ * F ((m + 1) * n) * r ^ ℓ` is at most
`(n.choose ℓ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ * ‖a 0‖` for `1 ≤ ℓ ≤ n`, then every zero
of `p` has norm at least `r`.

The paper's `r₁` is exactly the largest such `r`. -/
theorem le_norm_of_isRoot_kFib {p : ℂ[X]} {k : ℝ} {F : ℕ → ℝ} (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    (m : ℕ) (hdeg : 1 ≤ p.natDegree) {r : ℝ}
    (hcoeff : ∀ ℓ ∈ Icc 1 p.natDegree,
      ‖p.coeff ℓ‖ * F ((m + 1) * p.natDegree) * r ^ ℓ
        ≤ (p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            * ‖p.coeff 0‖)
    {z : ℂ} (hz : p.IsRoot z) : r ≤ ‖z‖ := by
  set n := p.natDegree with hn
  have hFnn := Real.kFib_nonneg hF0 hF1 hrec hk
  obtain ⟨t, ht⟩ : ∃ t, (m + 1) * n = t + 1 := ⟨(m + 1) * n - 1, by
    have : 1 ≤ (m + 1) * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩
  have hD : 0 < F ((m + 1) * n) := by
    rw [ht]; exact Real.kFib_pos hF0 hF1 hrec hk t
  have hNnn : ∀ ℓ, 0 ≤ (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ :=
    fun ℓ => mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (hFnn m) _)) (pow_nonneg (hFnn (m + 1)) _)) (hFnn ℓ)
  refine le_norm_of_isRoot_of_sum_weights
    (A := fun ℓ =>
      (n.choose ℓ : ℝ) * F m ^ (n - ℓ) * F (m + 1) ^ ℓ * F ℓ / F ((m + 1) * n))
    (fun ℓ => div_nonneg (hNnn ℓ) hD.le) ?_ ?_ hz
  · have hthm := Real.sum_choose_mul_kFib hF0 hF1 hrec m n
    have hins : range (n + 1) = insert 0 (Icc 1 n) := by
      ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hins, sum_insert (by simp)] at hthm
    have hzero : (n.choose 0 : ℝ) * F m ^ (n - 0) * F (m + 1) ^ 0 * F 0 = 0 := by
      rw [hF0, mul_zero]
    rw [hzero, zero_add] at hthm
    rw [← sum_div, hthm, div_self hD.ne']
  · intro ℓ hℓ
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    calc ‖p.coeff ℓ‖ * r ^ ℓ * F ((m + 1) * n)
        = ‖p.coeff ℓ‖ * F ((m + 1) * n) * r ^ ℓ := by ring
      _ ≤ _ := hcoeff ℓ hℓ

/-- Auxiliary `rpow` computation for the upper radius: if `R` dominates the `ℓ`-th root of
`D / Nl * (a / c)`, then `a * D ≤ Nl * (c * R ^ ℓ)`. -/
private lemma mul_le_of_rpow_le {D Nl a c R : ℝ} {ℓ : ℕ} (hD : 0 ≤ D) (hN : 0 < Nl)
    (ha : 0 ≤ a) (hc : 0 < c) (hℓ : ℓ ≠ 0)
    (hR : (D / Nl * (a / c)) ^ ((ℓ : ℝ)⁻¹) ≤ R) :
    a * D ≤ Nl * (c * R ^ ℓ) := by
  have hb0 : 0 ≤ D / Nl * (a / c) := by positivity
  have hpow : D / Nl * (a / c) ≤ R ^ ℓ :=
    calc D / Nl * (a / c) = ((D / Nl * (a / c)) ^ ((ℓ : ℝ)⁻¹)) ^ ℓ :=
          (Real.rpow_inv_natCast_pow hb0 hℓ).symm
      _ ≤ R ^ ℓ := pow_le_pow_left₀ (Real.rpow_nonneg hb0 _) hR ℓ
  calc a * D = Nl * c * (D / Nl * (a / c)) := by field_simp [hN.ne', hc.ne']
    _ ≤ Nl * c * R ^ ℓ := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Nl * (c * R ^ ℓ) := by ring

/-- Auxiliary `rpow` computation for the lower radius: if `r` is below the `ℓ`-th root of
`Nl / D * (a / c)`, then `c * D * r ^ ℓ ≤ Nl * a`. -/
private lemma mul_rpow_le_of_le {D Nl a c r : ℝ} {ℓ : ℕ} (hD : 0 < D) (hN : 0 ≤ Nl)
    (ha : 0 ≤ a) (hc : 0 < c) (hℓ : ℓ ≠ 0) (hr0 : 0 ≤ r)
    (hr : r ≤ (Nl / D * (a / c)) ^ ((ℓ : ℝ)⁻¹)) :
    c * D * r ^ ℓ ≤ Nl * a := by
  have hb0 : 0 ≤ Nl / D * (a / c) := by positivity
  have hpow : r ^ ℓ ≤ Nl / D * (a / c) :=
    calc r ^ ℓ
        ≤ ((Nl / D * (a / c)) ^ ((ℓ : ℝ)⁻¹)) ^ ℓ := pow_le_pow_left₀ hr0 hr ℓ
      _ = Nl / D * (a / c) := Real.rpow_inv_natCast_pow hb0 hℓ
  calc c * D * r ^ ℓ ≤ c * D * (Nl / D * (a / c)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Nl * a := by field_simp [hD.ne', hc.ne']

section Annulus

variable {p : ℂ[X]} {k : ℝ} {F : ℕ → ℝ}

/-- **Theorem 1.2** of the paper, upper radius in closed form: every zero of `p` has norm at
most the paper's
`r₂ = max_{1 ≤ ℓ ≤ n} (F ((m+1)n) / ((n.choose ℓ) * F m ^ (n-ℓ) * F (m+1) ^ ℓ * F ℓ)
  * ‖a (n-ℓ) / a n‖) ^ (1/ℓ)`.

Here `m` is one less than the paper's parameter, and the hypothesis `1 ≤ m` corresponds to the
paper's implicit assumption that `F (m-1) ≠ 0` (their radii divide by it). -/
theorem norm_le_kFib_sup_of_isRoot (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree) {z : ℂ} (hz : p.IsRoot z) :
    ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
      (F ((m + 1) * p.natDegree)
          / ((p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ)
          * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  set n := p.natDegree with hn
  have hFnn := Real.kFib_nonneg hF0 hF1 hrec hk
  have hp0 : p ≠ 0 := by
    intro h
    rw [hn, h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hlc : 0 < ‖p.leadingCoeff‖ := by simpa using leadingCoeff_ne_zero.2 hp0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hNpos : ∀ ℓ ∈ Icc 1 n,
      0 < (n.choose ℓ : ℝ) * F (m' + 1) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ := by
    intro ℓ hℓ
    simp only [mem_Icc] at hℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    have hFm : 0 < F (m' + 1) := Real.kFib_pos hF0 hF1 hrec hk m'
    have hFm1 : 0 < F (m' + 1 + 1) := Real.kFib_pos hF0 hF1 hrec hk (m' + 1)
    have hFℓ : 0 < F (ℓ' + 1) := Real.kFib_pos hF0 hF1 hrec hk ℓ'
    have hch : 0 < (n.choose (ℓ' + 1) : ℝ) := by exact_mod_cast Nat.choose_pos hℓ.2
    positivity
  refine norm_le_of_isRoot_kFib hk hF0 hF1 hrec (m' + 1) hdeg ?_ ?_ hz
  · refine le_trans ?_ (Finset.le_sup' _ (mem_Icc.2 ⟨hdeg, le_rfl⟩))
    exact Real.rpow_nonneg (mul_nonneg (div_nonneg (hFnn _) (hNpos n (mem_Icc.2
      ⟨hdeg, le_rfl⟩)).le) (div_nonneg (norm_nonneg _) (norm_nonneg _))) _
  · intro ℓ hℓ
    have hℓ0 : ℓ ≠ 0 := by simp only [mem_Icc] at hℓ; omega
    have hle := Finset.le_sup' (s := Icc 1 n) (f := fun ℓ =>
      (F ((m' + 1 + 1) * n)
          / ((n.choose ℓ : ℝ) * F (m' + 1) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ)
          * (‖p.coeff (n - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹)) hℓ
    exact mul_le_of_rpow_le (hFnn _) (hNpos ℓ hℓ) (norm_nonneg _) hlc hℓ0 hle

/-- **Theorem 1.2** of the paper, lower radius in closed form: every zero of `p` has norm at
least the paper's
`r₁ = min_{1 ≤ ℓ ≤ n} ((n.choose ℓ) * F m ^ (n-ℓ) * F (m+1) ^ ℓ * F ℓ / F ((m+1)n)
  * ‖a 0 / a ℓ‖) ^ (1/ℓ)`.

The hypothesis `ha` (`a ℓ ≠ 0` for `1 ≤ ℓ ≤ n`) is the paper's standing assumption. -/
theorem kFib_inf_le_norm_of_isRoot (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : ℂ} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
      ((p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
          / F ((m + 1) * p.natDegree)
          * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ := by
  set n := p.natDegree with hn
  have hFnn := Real.kFib_nonneg hF0 hF1 hrec hk
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, (m' + 1 + 1) * n = t + 1 := ⟨(m' + 1 + 1) * n - 1, by
    have : 1 ≤ (m' + 1 + 1) * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩
  have hD : 0 < F ((m' + 1 + 1) * n) := by
    rw [ht]; exact Real.kFib_pos hF0 hF1 hrec hk t
  have hr0 : 0 ≤ (Icc 1 n).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
      ((n.choose ℓ : ℝ) * F (m' + 1) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ
        / F ((m' + 1 + 1) * n) * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) := by
    refine Finset.le_inf' _ _ fun ℓ hℓ => ?_
    have hNnn :
        0 ≤ (n.choose ℓ : ℝ) * F (m' + 1) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (hFnn _) _)) (pow_nonneg (hFnn _) _)) (hFnn ℓ)
    exact Real.rpow_nonneg (mul_nonneg (div_nonneg hNnn hD.le)
      (div_nonneg (norm_nonneg _) (norm_nonneg _))) _
  refine le_norm_of_isRoot_kFib hk hF0 hF1 hrec (m' + 1) hdeg ?_ hz
  intro ℓ hℓ
  have hℓ0 : ℓ ≠ 0 := by simp only [mem_Icc] at hℓ; omega
  have hNnn : 0 ≤ (n.choose ℓ : ℝ) * F (m' + 1) ^ (n - ℓ) * F (m' + 1 + 1) ^ ℓ * F ℓ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (hFnn _) _)) (pow_nonneg (hFnn _) _)) (hFnn ℓ)
  have hc : 0 < ‖p.coeff ℓ‖ := norm_pos_iff.2 (ha ℓ hℓ)
  exact mul_rpow_le_of_le hD hNnn (norm_nonneg _) hc hℓ0 hr0 (Finset.inf'_le _ hℓ)

/-- **Theorem 1.2** of the paper: all zeros of `p` lie in the closed annulus
`r₁ ≤ ‖z‖ ≤ r₂` with the radii given by the `k`-Fibonacci expressions of the paper (see
`kFib_inf_le_norm_of_isRoot` and `norm_le_kFib_sup_of_isRoot` for the two halves). -/
theorem isRoot_mem_kFib_annulus (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    {m : ℕ} (hm : 1 ≤ m) (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : ℂ} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ
            / F ((m + 1) * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F ((m + 1) * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * F m ^ (p.natDegree - ℓ) * F (m + 1) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) :=
  ⟨kFib_inf_le_norm_of_isRoot hk hF0 hF1 hrec hm hdeg ha hz,
    norm_le_kFib_sup_of_isRoot hk hF0 hF1 hrec hm hdeg hz⟩

/-- **Corollary 1.3** of the paper (the main result of Bidkham–Shashahani): the case `m = 4`
in the paper's indexing, where `F 3 = k ^ 2 + 1` and `F 4 = k ^ 3 + 2 * k`. -/
theorem isRoot_mem_kFib_annulus_four (hk : 0 < k)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (hrec : ∀ j, F (j + 2) = k * F (j + 1) + F j)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : ℂ} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * (k ^ 2 + 1) ^ (p.natDegree - ℓ)
            * (k ^ 3 + 2 * k) ^ ℓ * F ℓ / F (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        (F (4 * p.natDegree)
            / ((p.natDegree.choose ℓ : ℝ) * (k ^ 2 + 1) ^ (p.natDegree - ℓ)
                * (k ^ 3 + 2 * k) ^ ℓ * F ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have h := isRoot_mem_kFib_annulus hk hF0 hF1 hrec (m := 3) (by norm_num) hdeg ha hz
  simpa only [Real.kFib_three hF0 hF1 hrec, Real.kFib_four hF0 hF1 hrec,
    show (3 : ℕ) + 1 = 4 from rfl] using h

/-- **Remark 1.4**: Diaz-Barrero's classical Fibonacci annulus, the case `k = 1`, `m = 4`
(paper indexing) of Theorem 1.2.  `Nat.fib` satisfies all the hypotheses, so no new
definition is required. -/
theorem isRoot_mem_fib_annulus (hdeg : 1 ≤ p.natDegree)
    (ha : ∀ ℓ ∈ Icc 1 p.natDegree, p.coeff ℓ ≠ 0) {z : ℂ} (hz : p.IsRoot z) :
    (Icc 1 p.natDegree).inf' (Finset.nonempty_Icc.2 hdeg) (fun ℓ =>
        ((p.natDegree.choose ℓ : ℝ) * 2 ^ (p.natDegree - ℓ) * 3 ^ ℓ * Nat.fib ℓ
            / Nat.fib (4 * p.natDegree)
            * (‖p.coeff 0‖ / ‖p.coeff ℓ‖)) ^ ((ℓ : ℝ)⁻¹)) ≤ ‖z‖ ∧
      ‖z‖ ≤ (Icc 1 p.natDegree).sup' (Finset.nonempty_Icc.2 hdeg) fun ℓ =>
        ((Nat.fib (4 * p.natDegree) : ℝ)
            / ((p.natDegree.choose ℓ : ℝ) * 2 ^ (p.natDegree - ℓ) * 3 ^ ℓ * Nat.fib ℓ)
            * (‖p.coeff (p.natDegree - ℓ)‖ / ‖p.leadingCoeff‖)) ^ ((ℓ : ℝ)⁻¹) := by
  have f3 : Nat.fib 3 = 2 := by decide
  have f4 : Nat.fib 4 = 3 := by decide
  have h := isRoot_mem_kFib_annulus (k := 1) (F := fun j => (Nat.fib j : ℝ)) one_pos
    (by exact_mod_cast Nat.fib_zero) (by exact_mod_cast Nat.fib_one)
    (fun j => by push_cast [Nat.fib_add_two]; ring) (m := 3) (by norm_num) hdeg ha hz
  simpa only [show (3 : ℕ) + 1 = 4 from rfl, f3, f4, Nat.cast_ofNat] using h

end Annulus

end Polynomial
