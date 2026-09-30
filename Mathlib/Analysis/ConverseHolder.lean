/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.PowerSumChain
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Converse Hölder and converse Cauchy inequalities for weighted power sums

This file proves the converse forms of Hölder's and Cauchy's inequalities used by Dujella,
Jakšetić and Pečarić (Theorems 8 and 9 of their paper), in weighted form.

* `Real.converse_holder_linear_of_one_lt`, `Real.converse_holder_linear_of_lt_one`: the linear
  converse Hölder inequality `(M - m) S u + (m M ^ p - M m ^ p) S v ≤ (M ^ p - m ^ p) S α` when
  `m ≤ x i ^ ((u - v) / p) ≤ M` (reversed for `0 < p < 1`).
* `Real.converse_holder_of_one_lt`, `Real.converse_holder_of_lt_one`: the multiplicative form
  `S u ^ (1 / p) * S v ^ (1 / q) ≤ λ * S α` (reversed for `0 < p < 1`).
* `Real.diaz_metcalf`, `Real.polya_szego`, `Real.shisha_mond`: converse Cauchy inequalities
  from ratio bounds `r * b i ≤ a i ≤ R * b i`, for arbitrary pairs.
* `Real.gram_le_of_sq_le`: if `(a i * b j - a j * b i) ^ 2 ≤ (c i - c j) ^ 2` and
  `lo ≤ c i ≤ hi`, then `A * B - C ^ 2 ≤ W ^ 2 * (hi - lo) ^ 2 / 4`.
* `Real.ozeki_rpow`: the Ozeki-type bound
  `A * B - C ^ 2 ≤ W ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2` for `a i = y i ^ σ`, `b i = y i ^ τ`.
* `Real.not_ozeki`: the same bound fails for arbitrary tuples, already for three terms.
* `Real.cauchy_conversion`: the four converse Cauchy inequalities of Dujella–Jakšetić–Pečarić,
  Theorem 9, for `a i = x i ^ (u / 2)` and `b i = x i ^ (v / 2)`, with weights.

## Implementation notes

Ozeki's inequality is often quoted for arbitrary tuples `m₁ ≤ a i ≤ M₁`, `m₂ ≤ b i ≤ M₂`, with the
constant `n ^ 2 / 4`.  `Real.not_ozeki` shows that this is false: `a = (10, 10, 1)` and
`b = (1, 10, 10)` give `A * B - C ^ 2 = 26001 > 22052.25`.  What the power-sum applications need
is the case in which `a i` and `b i` are powers of the same number `y i`, and there the bound
holds (`Real.ozeki_rpow`).  If `σ` and `τ` have the same sign, the Lagrange terms
`a i * b j - a j * b i` are dominated by the differences of `c i = y i ^ (σ + τ)`; if they have
opposite signs, the points `(a i, b i)` lie below the chord joining the extreme points, by
convexity of `y ↦ A * y ^ σ + B * y ^ τ` in `log y`, and a projective change of variables
reduces to the same comparison.  In both cases Popoviciu's variance bound finishes the proof.
-/

@[expose] public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-! ### Converse Hölder -/

/-- **Linear converse Hölder inequality**, `p > 1`: if `m ≤ x i ^ ((u - v) / p) ≤ M`, then
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * S α`. -/
theorem converse_holder_linear_of_one_lt {p q u v α m M : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v ≤
      (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α := by
  sorry

/-- **Linear converse Hölder inequality**, `0 < p < 1`: the inequality of
`Real.converse_holder_linear_of_one_lt` reverses. -/
theorem converse_holder_linear_of_lt_one {p q u v α m M : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α ≤
      (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v := by
  sorry

/-- **Converse Hölder inequality**, `p > 1`: if `0 < m < M` and `m ≤ x i ^ ((u - v) / p) ≤ M`,
then `S u ^ (1 / p) * S v ^ (1 / q) ≤ λ * S α` with
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`. -/
theorem converse_holder_of_one_lt {p q u v α m M : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hmM : m < M) (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α := by
  sorry

/-- **Converse Hölder inequality**, `0 < p < 1`: the inequality of
`Real.converse_holder_of_one_lt` reverses (both `q` and `m * M ^ p - M * m ^ p` are then
negative, so `λ` is still positive). -/
theorem converse_holder_of_lt_one {p q u v α m M : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m) (hmM : m < M)
    (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
  sorry

/-! ### Converse Cauchy inequalities from ratio bounds -/

variable {a b : ι → ℝ} {r R : ℝ}

/-- **Diaz–Metcalf inequality**: if `r * b i ≤ a i ≤ R * b i`, then
`∑ w a ^ 2 + r * R * ∑ w b ^ 2 ≤ (r + R) * ∑ w a b`. -/
theorem diaz_metcalf (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, r * b i ≤ a i)
    (hR : ∀ i ∈ s, a i ≤ R * b i) :
    ∑ i ∈ s, w i * a i ^ 2 + r * R * ∑ i ∈ s, w i * b i ^ 2 ≤
      (r + R) * ∑ i ∈ s, w i * (a i * b i) := by
  sorry

/-- **Pólya–Szegő inequality**: if `0 < r`, `r * b i ≤ a i ≤ R * b i`, then
`(∑ w a ^ 2) * (∑ w b ^ 2) ≤ (r + R) ^ 2 / (4 * r * R) * (∑ w a b) ^ 2`. -/
theorem polya_szego (hw : ∀ i ∈ s, 0 ≤ w i) (hr0 : 0 < r) (hr : ∀ i ∈ s, r * b i ≤ a i)
    (hR : ∀ i ∈ s, a i ≤ R * b i) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) ≤
      (r + R) ^ 2 / (4 * r * R) * (∑ i ∈ s, w i * (a i * b i)) ^ 2 := by
  sorry

/-- **Shisha–Mond inequality**: if `0 < r`, `r * b i ≤ a i ≤ R * b i` and the sums
`∑ w a b`, `∑ w b ^ 2` are positive, then
`∑ w a ^ 2 / ∑ w a b - ∑ w a b / ∑ w b ^ 2 ≤ (√R - √r) ^ 2`. -/
theorem shisha_mond (hw : ∀ i ∈ s, 0 ≤ w i) (hr0 : 0 < r) (hr : ∀ i ∈ s, r * b i ≤ a i)
    (hR : ∀ i ∈ s, a i ≤ R * b i) (hC : 0 < ∑ i ∈ s, w i * (a i * b i))
    (hB : 0 < ∑ i ∈ s, w i * b i ^ 2) :
    (∑ i ∈ s, w i * a i ^ 2) / (∑ i ∈ s, w i * (a i * b i)) -
        (∑ i ∈ s, w i * (a i * b i)) / (∑ i ∈ s, w i * b i ^ 2) ≤
      (√R - √r) ^ 2 := by
  sorry

/-! ### Ozeki-type bounds -/

/-- **Lagrange–Popoviciu bound**: if every Lagrange term `a i * b j - a j * b i` is dominated
by `c i - c j`, and `lo ≤ c i ≤ hi`, then
`(∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2 ≤ (∑ w) ^ 2 * (hi - lo) ^ 2 / 4`. -/
theorem gram_le_of_sq_le {c : ι → ℝ} {lo hi : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hc : ∀ i ∈ s, lo ≤ c i ∧ c i ≤ hi)
    (hdom : ∀ i ∈ s, ∀ j ∈ s, (a i * b j - a j * b i) ^ 2 ≤ (c i - c j) ^ 2) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) - (∑ i ∈ s, w i * (a i * b i)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 * (hi - lo) ^ 2 / 4 := by
  sorry

/-- **Ozeki-type bound for powers of one sequence**: if `0 < lo ≤ y i ≤ hi`, `a i = y i ^ σ`
and `b i = y i ^ τ`, then
`(∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2 ≤ (∑ w) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2`, where
`m₁, M₁` are the smaller and larger of `lo ^ σ`, `hi ^ σ`, and `m₂, M₂` those of `lo ^ τ`,
`hi ^ τ`. -/
theorem ozeki_rpow {y : ι → ℝ} {lo hi σ τ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hlo : 0 < lo)
    (hy : ∀ i ∈ s, lo ≤ y i ∧ y i ≤ hi) :
    (∑ i ∈ s, w i * (y i ^ σ) ^ 2) * (∑ i ∈ s, w i * (y i ^ τ) ^ 2) -
        (∑ i ∈ s, w i * (y i ^ σ * y i ^ τ)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ σ) (hi ^ σ) * max (lo ^ τ) (hi ^ τ) -
          min (lo ^ σ) (hi ^ σ) * min (lo ^ τ) (hi ^ τ)) ^ 2 := by
  sorry

/-- **Ozeki's inequality fails for arbitrary tuples**: there are `a, b : Fin 3 → ℝ` with
`1 ≤ a i ≤ 10` and `1 ≤ b i ≤ 10` for which
`(∑ a ^ 2) * (∑ b ^ 2) - (∑ a b) ^ 2 > 3 ^ 2 / 4 * (10 * 10 - 1 * 1) ^ 2`. -/
theorem not_ozeki :
    ¬ ∀ (a b : Fin 3 → ℝ) (m₁ M₁ m₂ M₂ : ℝ), 0 < m₁ → 0 < m₂ →
      (∀ i, m₁ ≤ a i ∧ a i ≤ M₁) → (∀ i, m₂ ≤ b i ∧ b i ≤ M₂) →
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 ≤
        (3 : ℝ) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  sorry

/-! ### The converse Cauchy inequalities for power sums -/

/-- **Converse Cauchy inequalities for weighted power sums** (Dujella–Jakšetić–Pečarić,
Theorem 9, for `w = 1`).  Let `0 < lo ≤ x i ≤ hi`, `α = u / 2 + v / 2`, and let `m₁, M₁`
(resp. `m₂, M₂`) be the smaller and larger of `lo ^ (u / 2)`, `hi ^ (u / 2)` (resp. of
`lo ^ (v / 2)`, `hi ^ (v / 2)`).  Then
1. `1 ≤ S u * S v / S α ^ 2 ≤ (√(M₁ M₂ / (m₁ m₂)) + √(m₁ m₂ / (M₁ M₂))) ^ 2 / 4`;
2. `S u / S α - S α / S v ≤ (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2`;
3. `S u * S v - S α ^ 2 ≤ W ^ 2 / 4 * (M₁ M₂ - m₁ m₂) ^ 2`;
4. `S v + m₂ M₂ / (M₁ m₁) * S u ≤ (M₂ / m₁ + m₂ / M₁) * S α`. -/
theorem cauchy_conversion {u v α lo hi m₁ M₁ m₂ M₂ : ℝ} (hα : u / 2 + v / 2 = α)
    (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i) (hlo : 0 < lo)
    (hx : ∀ i ∈ s, lo ≤ x i ∧ x i ≤ hi)
    (hm₁ : m₁ = min (lo ^ (u / 2)) (hi ^ (u / 2))) (hM₁ : M₁ = max (lo ^ (u / 2)) (hi ^ (u / 2)))
    (hm₂ : m₂ = min (lo ^ (v / 2)) (hi ^ (v / 2))) (hM₂ : M₂ = max (lo ^ (v / 2)) (hi ^ (v / 2))) :
    (1 ≤ (∑ i ∈ s, w i * x i ^ u) * (∑ i ∈ s, w i * x i ^ v) / (∑ i ∈ s, w i * x i ^ α) ^ 2 ∧
      (∑ i ∈ s, w i * x i ^ u) * (∑ i ∈ s, w i * x i ^ v) / (∑ i ∈ s, w i * x i ^ α) ^ 2 ≤
        (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4) ∧
    (∑ i ∈ s, w i * x i ^ u) / (∑ i ∈ s, w i * x i ^ α) -
        (∑ i ∈ s, w i * x i ^ α) / (∑ i ∈ s, w i * x i ^ v) ≤
      (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2 ∧
    (∑ i ∈ s, w i * x i ^ u) * (∑ i ∈ s, w i * x i ^ v) - (∑ i ∈ s, w i * x i ^ α) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 ∧
    ∑ i ∈ s, w i * x i ^ v + m₂ * M₂ / (M₁ * m₁) * ∑ i ∈ s, w i * x i ^ u ≤
      (M₂ / m₁ + m₂ / M₁) * ∑ i ∈ s, w i * x i ^ α := by
  sorry

end Real
