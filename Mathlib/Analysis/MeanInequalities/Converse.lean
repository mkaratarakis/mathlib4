/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Lagrange
public import Mathlib.Analysis.Convex.ConverseJensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.MeanInequalities.PowerSum
public import Mathlib.Analysis.Real.Sqrt

/-!
# Converse Hölder and converse Cauchy–Schwarz inequalities for weighted power sums

For weights `w i ≥ 0` and positive reals `x i`, `i ∈ s`, write `S γ = ∑ i ∈ s, w i * x i ^ γ` for
the weighted power sum of exponent `γ`, and `W = ∑ i ∈ s, w i`. Hölder's inequality bounds `S α`,
`α = u / p + v / q`, by `S u ^ (1 / p) * S v ^ (1 / q)`; this file bounds it from the other side
when the ratios `x i ^ ((u - v) / p)` lie in an interval `[m, M]`, and bounds
`S u * S v` from above in terms of `S ((u + v) / 2) ^ 2` (converse Cauchy–Schwarz). For families
`c`, `r` we abbreviate `∑ i ∈ s, c i * r i ^ p` to `∑ c r ^ p`, and similarly for other sums.

## Main results

* `Real.converse_holder_linear_of_one_le`, `Real.converse_holder_linear_of_le_one`: the
  Lah–Ribarič inequality (`ConvexOn.lah_ribaric`, `ConcaveOn.lah_ribaric` in
  `Mathlib.Analysis.Convex.ConverseJensen`) for the function `r ↦ r ^ p`: for `c i ≥ 0` and
  `r i ∈ [m, M]` with `0 ≤ m`,
  `(M - m) * ∑ c r ^ p + (m * M ^ p - M * m ^ p) * ∑ c ≤ (M ^ p - m ^ p) * ∑ c r` for `p ≥ 1`,
  and the reverse inequality for `0 ≤ p ≤ 1`.
* `Real.converse_holder_of_one_lt`, `Real.converse_holder_of_lt_one`: if moreover `0 < m < M`,
  then `(∑ c r ^ p) ^ (1 / p) * (∑ c) ^ (1 / q) ≤ λ * ∑ c r` for conjugate exponents `p`, `q`
  with `p > 1`, and the reverse inequality for `0 < p < 1`, where
  `λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`.
* `Real.converse_holder_linear_rpow_of_one_lt`, `Real.converse_holder_rpow_of_one_lt`, ...: the
  case `c i = w i * x i ^ v`, `r i = x i ^ ((u - v) / p)` of power sums, where `∑ c r ^ p = S u`,
  `∑ c = S v` and `∑ c r = S α`.
* `Real.shisha_mond`: the **Shisha–Mond inequality**: if `r * b i ≤ a i ≤ R * b i` with `0 ≤ r`,
  `0 ≤ R`, then `∑ w a ^ 2 / ∑ w a b - ∑ w a b / ∑ w b ^ 2 ≤ (√R - √r) ^ 2`.
* `Real.polya_szego`: the **Pólya–Szegő inequality** for `a i ∈ [m₁, M₁]`, `b i ∈ [m₂, M₂]` with
  `0 < m₁`, `0 < m₂`:
  `(∑ w a ^ 2) * (∑ w b ^ 2) ≤ (√(M₁ M₂ / (m₁ m₂)) + √(m₁ m₂ / (M₁ M₂))) ^ 2 / 4 * (∑ w a b) ^ 2`.
* `Real.rpow_mem_uIcc`: if `z` lies between the positive reals `x` and `y`, then `z ^ e` lies
  between `x ^ e` and `y ^ e`.
* `Real.monovaryOn_rpow_rpow`: `y ^ σ` and `y ^ τ` monovary when `σ` and `τ` have the same sign.
* `Real.sq_sum_mul_rpow_add_div_two_le`: the Cauchy–Schwarz inequality
  `S ((u + v) / 2) ^ 2 ≤ S u * S v` for powers of one positive family `y`.
* `Real.polya_szego_rpow`, `Real.shisha_mond_rpow`, `Real.ozeki_rpow`, `Real.diaz_metcalf_rpow`:
  converse Cauchy–Schwarz inequalities between `S u`, `S v` and `S ((u + v) / 2)` for powers of
  one positive family `y`, from the bounds `y i ^ (u / 2) ∈ [m₁, M₁]`, `y i ^ (v / 2) ∈ [m₂, M₂]`
  with `0 < m₁` and `0 < m₂` (for Shisha–Mond `0 ≤ m₁` suffices, for Diaz–Metcalf `0 ≤ m₂`).
  For **Ozeki**'s inequality `S u * S v - S ((u + v) / 2) ^ 2 ≤ W ^ 2 / 4 * (M₁ M₂ - m₁ m₂) ^ 2`
  the bounds are the values at the endpoints of an interval `[lo, hi]` with `0 < lo` containing
  every `y i`.
* `Real.ozeki_rpow_eq`: the constant `W ^ 2 / 4` in `Real.ozeki_rpow` cannot be improved; equality
  holds for `u = 2`, `v = -2` when the `y i` take only the values `lo` and `hi`, each with total
  weight `W / 2`.

Dujella, Jakšetić and Pečarić apply these inequalities in the unweighted case `w = 1` (their
Theorems 8 and 9). The Diaz–Metcalf and Cassels inequalities for ratio bounds and the
Lagrange–Popoviciu bound, which hold in any linearly ordered commutative ring, are in
`Mathlib.Algebra.Order.BigOperators.Ring.Lagrange`.

## Implementation notes

Ozeki's inequality is often quoted for arbitrary families `m₁ ≤ a i ≤ M₁`, `m₂ ≤ b i ≤ M₂` of `n`
positive reals with the constant `n ^ 2 / 4`. In this form it is false, as Izumino and Seo, and
Izumino, Mori and Seo, observed (see `Counterexamples/Ozeki.lean` for a three-term example).
Izumino, Mori and Seo determined the best constant: it is `n ^ 2 / 3` when `3 ∣ n` and
`(n ^ 2 - 1) / 3` otherwise, so `n ^ 2 / 4` is best only for `n = 2`. The constant `n ^ 2 / 4`
does hold when `a i = y i ^ σ` and `b i = y i ^ τ` are powers of one family (`Real.ozeki_rpow`).
If `σ` and `τ` have the same sign, then `a` and `b` monovary
(`Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_monovaryOn`); if they have opposite
signs, then the points `(a i, b i)` lie below the line through the extreme points, by convexity
of `t ↦ A * exp (σ * t) + B * exp (τ * t)` for `A, B ≥ 0`
(`Finset.four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_mul_add_mul_le`).

## References

* [A. Dujella, J. Jakšetić and J. Pečarić, *Fibonacci numbers and Hölder inequality*]
  [dujella_jaksetic_pecaric]
* [O. Shisha and B. Mond, *Bounds on differences of means*][shisha_mond_1967]
* [G. Pólya and G. Szegő, *Aufgaben und Lehrsätze aus der Analysis. Band I*][polya_szego_1925]
* [J. B. Diaz and F. T. Metcalf, *Stronger forms of a class of inequalities of G. Pólya–G. Szegő,
  and L. V. Kantorovich*][diaz_metcalf_1963]
* [G. S. Watson, *Serial correlation in regression analysis. I*][watson_1955]
* [N. Ozeki, *On the estimation of the inequalities by the maximum, or minimum values*]
  [ozeki_1968]
* [S. Izumino and Y. Seo, *Ozeki's inequality and noncommutative covariance*][izumino_seo_1997]
* [S. Izumino, H. Mori and Y. Seo, *On Ozeki's inequality*][izumino_mori_seo_1998]
-/

public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-! ### Converse Hölder -/

section ConverseHolder

variable {c r : ι → ℝ} {p q m M : ℝ}

/-- **Linear converse Hölder inequality**, `p ≥ 1`: for `c i ≥ 0` and `r i ∈ [m, M]` with
`0 ≤ m`, `(M - m) * ∑ c r ^ p + (m * M ^ p - M * m ^ p) * ∑ c ≤ (M ^ p - m ^ p) * ∑ c r`. -/
theorem converse_holder_linear_of_one_le (hp : 1 ≤ p) (hc : ∀ i ∈ s, 0 ≤ c i) (hm : 0 ≤ m)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc m M) :
    (M - m) * ∑ i ∈ s, c i * r i ^ p + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, c i ≤
      (M ^ p - m ^ p) * ∑ i ∈ s, c i * r i :=
  ((convexOn_rpow hp).subset (fun _ hx ↦ hm.trans hx.1) (convex_Icc m M)).lah_ribaric s hc hr

/-- **Linear converse Hölder inequality**, `0 ≤ p ≤ 1`: for `c i ≥ 0` and `r i ∈ [m, M]` with
`0 ≤ m`, `(M ^ p - m ^ p) * ∑ c r ≤ (M - m) * ∑ c r ^ p + (m * M ^ p - M * m ^ p) * ∑ c`. -/
theorem converse_holder_linear_of_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hm : 0 ≤ m) (hr : ∀ i ∈ s, r i ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * ∑ i ∈ s, c i * r i ≤
      (M - m) * ∑ i ∈ s, c i * r i ^ p + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, c i :=
  ((concaveOn_rpow hp0 hp1).subset (fun _ hx ↦ hm.trans hx.1) (convex_Icc m M)).lah_ribaric s hc
    hr

/-- Rescaling by `A, B > 0`: `X ^ (1 / p) * Y ^ (1 / q) =
A ^ (-1 / p) * B ^ (-1 / q) * ((A * X) ^ (1 / p) * (B * Y) ^ (1 / q))`. -/
private lemma rpow_one_div_mul_rpow_one_div_eq {A B X Y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    X ^ (1 / p) * Y ^ (1 / q) =
      A ^ (-1 / p) * B ^ (-1 / q) * ((A * X) ^ (1 / p) * (B * Y) ^ (1 / q)) := by
  rw [mul_rpow hA.le hX, mul_rpow hB.le hY, neg_div, neg_div, rpow_neg hA.le, rpow_neg hB.le]
  have := rpow_pos_of_pos hA (1 / p)
  have := rpow_pos_of_pos hB (1 / q)
  field_simp

/-- **Converse Hölder inequality**, `p > 1`: for conjugate exponents `p`, `q`, `c i ≥ 0` and
`r i ∈ [m, M]` with `0 < m < M`, `(∑ c r ^ p) ^ (1 / p) * (∑ c) ^ (1 / q) ≤ λ * ∑ c r`, where
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`. -/
theorem converse_holder_of_one_lt (hpq : p.HolderConjugate q) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hm : 0 < m) (hmM : m < M) (hr : ∀ i ∈ s, r i ∈ Set.Icc m M) :
    (∑ i ∈ s, c i * r i ^ p) ^ (1 / p) * (∑ i ∈ s, c i) ^ (1 / q) ≤
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, c i * r i := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hM : 0 < M := hm.trans hmM
  have hA : 0 < p * (M - m) := mul_pos hp (sub_pos.2 hmM)
  have hB : 0 < q * (m * M ^ p - M * m ^ p) := by
    have h1 : m ^ (p - 1) < M ^ (p - 1) := rpow_lt_rpow hm.le hmM (sub_pos.2 hpq.lt)
    rw [rpow_sub_one hm.ne', rpow_sub_one hM.ne', div_lt_div_iff₀ hm hM] at h1
    nlinarith
  have hSu : 0 ≤ ∑ i ∈ s, c i * r i ^ p :=
    sum_nonneg fun i hi ↦ mul_nonneg (hc i hi) (rpow_nonneg (hm.le.trans (hr i hi).1) _)
  have hSv : 0 ≤ ∑ i ∈ s, c i := sum_nonneg hc
  -- weighted AM-GM with weights `1 / p`, `1 / q`
  have hamgm := geom_mean_le_arith_mean2_weighted (by positivity : 0 ≤ 1 / p)
    (by positivity : 0 ≤ 1 / q) (mul_nonneg hA.le hSu) (mul_nonneg hB.le hSv)
    (by simpa only [one_div] using hpq.inv_add_inv_eq_one)
  rw [rpow_one_div_mul_rpow_one_div_eq hA hB hSu hSv]
  calc _ ≤ (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ((M ^ p - m ^ p) * ∑ i ∈ s, c i * r i) := by
        refine mul_le_mul_of_nonneg_left (hamgm.trans ?_) (by positivity)
        convert converse_holder_linear_of_one_le s hpq.lt.le hc hm.le hr using 1
        field_simp
    _ = _ := by ring

/-- **Converse Hölder inequality**, `0 < p < 1`: for `p⁻¹ + q⁻¹ = 1`, `c i ≥ 0` and
`r i ∈ [m, M]` with `0 < m < M`, `λ * ∑ c r ≤ (∑ c r ^ p) ^ (1 / p) * (∑ c) ^ (1 / q)`, where
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`.
Both `q` and `m * M ^ p - M * m ^ p` are negative here, so `λ` is positive. -/
theorem converse_holder_of_lt_one (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hm : 0 < m) (hmM : m < M) (hr : ∀ i ∈ s, r i ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, c i * r i ≤
      (∑ i ∈ s, c i * r i ^ p) ^ (1 / p) * (∑ i ∈ s, c i) ^ (1 / q) := by
  have hq := neg_of_lt_one_of_inv_add_inv_eq_one hp0 hp1 hpq
  have hM : 0 < M := hm.trans hmM
  have hA : 0 < p * (M - m) := mul_pos hp0 (sub_pos.2 hmM)
  have hB : 0 < q * (m * M ^ p - M * m ^ p) := by
    have h1 : M ^ (p - 1) < m ^ (p - 1) := rpow_lt_rpow_of_neg hm hmM (by linarith)
    rw [rpow_sub_one hm.ne', rpow_sub_one hM.ne', div_lt_div_iff₀ hM hm] at h1
    nlinarith
  have hSu : 0 ≤ ∑ i ∈ s, c i * r i ^ p :=
    sum_nonneg fun i hi ↦ mul_nonneg (hc i hi) (rpow_nonneg (hm.le.trans (hr i hi).1) _)
  obtain hSv | hSv := (sum_nonneg hc).eq_or_lt
  · -- if `∑ c = 0`, then all `c i` vanish and the left-hand side is zero
    rw [sum_mul_eq_zero_of_sum_eq_zero hc hSv.symm r, mul_zero]
    exact mul_nonneg (rpow_nonneg hSu _) (rpow_nonneg hSv.le _)
  -- reverse Young inequality with exponents `p`, `q`
  have hy := div_add_div_le_rpow_mul_rpow_of_lt_one (mul_nonneg hA.le hSu) (mul_pos hB hSv) hp0
    hp1 hpq
  rw [rpow_one_div_mul_rpow_one_div_eq hA hB hSu hSv.le]
  calc _ = (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ((M ^ p - m ^ p) * ∑ i ∈ s, c i * r i) := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ((converse_holder_linear_of_le_one s hp0.le hp1.le hc
          hm.le hr).trans (le_of_eq_of_le ?_ hy)) (by positivity)
        field_simp [hq.ne]

end ConverseHolder

/-! ### Converse Hölder for power sums -/

section PowerSum

variable {p q u v α m M : ℝ}

/-- The exponent bookkeeping behind the converse Hölder inequalities for power sums: with
`c i = w i * x i ^ v` and `r i = x i ^ ((u - v) / p)`, `S u = ∑ c r ^ p` and `S α = ∑ c r`. -/
private lemma sum_mul_rpow_eq_sum_mul_rpow_mul (hp : p ≠ 0) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ u = ∑ i ∈ s, w i * x i ^ v * (x i ^ ((u - v) / p)) ^ p ∧
      ∑ i ∈ s, w i * x i ^ α = ∑ i ∈ s, w i * x i ^ v * x i ^ ((u - v) / p) := by
  have hαe : α = v + (u - v) / p := by
    rw [← hα, div_eq_mul_inv v q, show q⁻¹ = 1 - p⁻¹ by linarith]; ring
  refine ⟨sum_congr rfl fun i hi ↦ ?_, sum_congr rfl fun i hi ↦ ?_⟩
  · rw [mul_assoc, ← rpow_mul (hx i hi).le, div_mul_cancel₀ _ hp, ← rpow_add (hx i hi),
      add_sub_cancel]
  · rw [mul_assoc, ← rpow_add (hx i hi), hαe]

/-- **Linear converse Hölder inequality for power sums**, `p > 1`: for conjugate exponents `p`,
`q`, `α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 ≤ m`,
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * S α`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem converse_holder_linear_rpow_of_one_lt (hpq : p.HolderConjugate q)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 ≤ m)
    (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v ≤
      (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α := by
  obtain ⟨hu, hα'⟩ :=
    sum_mul_rpow_eq_sum_mul_rpow_mul s hpq.ne_zero hpq.inv_add_inv_eq_one hα hx (w := w)
  rw [hu, hα']
  exact converse_holder_linear_of_one_le s hpq.lt.le
    (fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le v)) hm hr

/-- **Linear converse Hölder inequality for power sums**, `0 < p < 1`: for `p⁻¹ + q⁻¹ = 1`,
`α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 ≤ m`,
`(M ^ p - m ^ p) * S α ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem converse_holder_linear_rpow_of_lt_one (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 ≤ m) (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α ≤
      (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v := by
  obtain ⟨hu, hα'⟩ := sum_mul_rpow_eq_sum_mul_rpow_mul s hp0.ne' hpq hα hx (w := w)
  rw [hu, hα']
  exact converse_holder_linear_of_le_one s hp0.le hp1.le
    (fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le v)) hm hr

/-- **Converse Hölder inequality for power sums**, `p > 1`: for conjugate exponents `p`, `q`,
`α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 < m < M`,
`S u ^ (1 / p) * S v ^ (1 / q) ≤ λ * S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`. -/
theorem converse_holder_rpow_of_one_lt (hpq : p.HolderConjugate q) (hα : u / p + v / q = α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m) (hmM : m < M)
    (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α := by
  obtain ⟨hu, hα'⟩ :=
    sum_mul_rpow_eq_sum_mul_rpow_mul s hpq.ne_zero hpq.inv_add_inv_eq_one hα hx (w := w)
  rw [hu, hα']
  exact converse_holder_of_one_lt s hpq
    (fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le v)) hm hmM hr

/-- **Converse Hölder inequality for power sums**, `0 < p < 1`: for `p⁻¹ + q⁻¹ = 1`,
`α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 < m < M`,
`λ * S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`. -/
theorem converse_holder_rpow_of_lt_one (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hmM : m < M) (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
  obtain ⟨hu, hα'⟩ := sum_mul_rpow_eq_sum_mul_rpow_mul s hp0.ne' hpq hα hx (w := w)
  rw [hu, hα']
  exact converse_holder_of_lt_one s hp0 hp1 hpq
    (fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le v)) hm hmM hr

end PowerSum

/-! ### Converse Cauchy–Schwarz -/

section ConverseCauchySchwarz

variable {a b : ι → ℝ} {r R m₁ M₁ m₂ M₂ : ℝ}

/-- **Shisha–Mond inequality**: if `w i ≥ 0`, `0 ≤ r`, `0 ≤ R` and `r * b i ≤ a i ≤ R * b i`, then
`∑ w a ^ 2 / ∑ w a b - ∑ w a b / ∑ w b ^ 2 ≤ (√R - √r) ^ 2`. -/
theorem shisha_mond (hw : ∀ i ∈ s, 0 ≤ w i) (hr0 : 0 ≤ r) (hR0 : 0 ≤ R)
    (hr : ∀ i ∈ s, r * b i ≤ a i) (hR : ∀ i ∈ s, a i ≤ R * b i) :
    (∑ i ∈ s, w i * a i ^ 2) / (∑ i ∈ s, w i * (a i * b i)) -
        (∑ i ∈ s, w i * (a i * b i)) / (∑ i ∈ s, w i * b i ^ 2) ≤
      (√R - √r) ^ 2 := by
  -- every `a i * b i` is nonnegative, so `∑ w a b ≥ 0`
  have hab : ∀ i ∈ s, 0 ≤ a i * b i := fun i hi ↦ by
    have h1 := hr i hi
    have h2 := hR i hi
    rcases le_total 0 (b i) with hb | hb
    · nlinarith [mul_nonneg hr0 (mul_self_nonneg (b i))]
    · nlinarith [mul_nonneg hR0 (mul_self_nonneg (b i))]
  obtain hC | hC := (sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (hab i hi)).eq_or_lt
  · rw [← hC, div_zero, zero_div, sub_zero]
    positivity
  -- some `w i * a i * b i` is nonzero, so `∑ w b ^ 2 > 0`
  have hB : 0 < ∑ i ∈ s, w i * b i ^ 2 := by
    obtain ⟨i, hi, hwi⟩ := exists_ne_zero_of_sum_ne_zero hC.ne'
    have hw' : 0 < w i := (hw i hi).lt_of_ne (left_ne_zero_of_mul hwi).symm
    have hb : b i ≠ 0 := fun h ↦ hwi (by simp [h])
    exact sum_pos' (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _)) ⟨i, hi, by positivity⟩
  have h1 := mul_le_mul_of_nonneg_right (diaz_metcalf hw hr hR) hB.le
  rw [← sq_sqrt hr0, ← sq_sqrt hR0] at h1
  rw [div_sub_div _ _ hC.ne' hB.ne', div_le_iff₀ (mul_pos hC hB)]
  nlinarith [sq_nonneg (√r * √R * ∑ i ∈ s, w i * b i ^ 2 - ∑ i ∈ s, w i * (a i * b i))]

/-- **Pólya–Szegő inequality**: if `w i ≥ 0`, `0 < m₁ ≤ a i ≤ M₁` and `0 < m₂ ≤ b i ≤ M₂`, then
`(∑ w a ^ 2) * (∑ w b ^ 2) ≤
(√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 * (∑ w a b) ^ 2`. -/
theorem polya_szego (hw : ∀ i ∈ s, 0 ≤ w i) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (ha : ∀ i ∈ s, a i ∈ Set.Icc m₁ M₁) (hb : ∀ i ∈ s, b i ∈ Set.Icc m₂ M₂) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) ≤
      (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 *
        (∑ i ∈ s, w i * (a i * b i)) ^ 2 := by
  obtain rfl | ⟨i₀, hi₀⟩ := s.eq_empty_or_nonempty
  · simp
  have hM₁ : 0 < M₁ := hm₁.trans_le ((ha i₀ hi₀).1.trans (ha i₀ hi₀).2)
  have hM₂ : 0 < M₂ := hm₂.trans_le ((hb i₀ hi₀).1.trans (hb i₀ hi₀).2)
  have h := cassels hw (fun i hi ↦ div_mul_le_of_le_of_le hm₁.le hM₂.le (ha i hi).1 (hb i hi).2)
    fun i hi ↦ le_div_mul_of_le_of_le hM₁.le hm₂ (ha i hi).2 (hb i hi).1
  -- the constant is `(r + R) ^ 2 / (4 * r * R)` for the ratio bounds `r = m₁ / M₂`, `R = M₁ / m₂`
  have h1 : √(M₁ * M₂ / (m₁ * m₂)) * √(m₁ * m₂ / (M₁ * M₂)) = 1 := by
    rw [← sqrt_mul (by positivity),
      show M₁ * M₂ / (m₁ * m₂) * (m₁ * m₂ / (M₁ * M₂)) = 1 by field_simp, sqrt_one]
  have hK : (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 =
      (m₁ / M₂ + M₁ / m₂) ^ 2 / (4 * (m₁ / M₂ * (M₁ / m₂))) := by
    rw [add_sq, sq_sqrt (by positivity), sq_sqrt (by positivity), mul_assoc, h1]
    field_simp
    ring
  rw [hK, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

end ConverseCauchySchwarz

/-! ### Powers of one family -/

/-- If `z` lies between the positive reals `x` and `y`, then `z ^ e` lies between `x ^ e` and
`y ^ e`. -/
theorem rpow_mem_uIcc {x y z : ℝ} (e : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : z ∈ Set.uIcc x y) :
    z ^ e ∈ Set.uIcc (x ^ e) (y ^ e) := by
  have hsub : Set.uIcc x y ⊆ Set.Ioi 0 := fun _ ha ↦ (lt_min hx hy).trans_le ha.1
  obtain he | he := le_total 0 e
  · exact ((monotoneOn_rpow_Ici_of_exponent_nonneg he).mono
      (hsub.trans Set.Ioi_subset_Ici_self)).mapsTo_uIcc hz
  · exact ((antitoneOn_rpow_Ioi_of_exponent_nonpos he).mono hsub).mapsTo_uIcc hz

/-- Powers `y ^ σ` and `y ^ τ` of a positive family `y` monovary if `σ` and `τ` have the same
sign, that is, if `0 ≤ σ * τ`. -/
theorem monovaryOn_rpow_rpow {s : Set ι} {y : ι → ℝ} {σ τ : ℝ} (hy : ∀ i ∈ s, 0 < y i)
    (hστ : 0 ≤ σ * τ) : MonovaryOn (y · ^ σ) (y · ^ τ) s := by
  have him : y '' s ⊆ Set.Ioi 0 := by rintro _ ⟨i, hi, rfl⟩; exact hy i hi
  obtain ⟨hσ, hτ⟩ | ⟨hσ, hτ⟩ := mul_nonneg_iff.1 hστ
  · exact (((monovaryOn_self y s).comp_monotoneOn_right
      ((monotoneOn_rpow_Ici_of_exponent_nonneg hτ).mono
        (him.trans Set.Ioi_subset_Ici_self))).symm.comp_monotoneOn_right
      ((monotoneOn_rpow_Ici_of_exponent_nonneg hσ).mono (him.trans Set.Ioi_subset_Ici_self))).symm
  · exact (((monovaryOn_self y s).comp_antitoneOn_right
      ((antitoneOn_rpow_Ioi_of_exponent_nonpos hτ).mono him)).symm.comp_antitoneOn_right
      ((antitoneOn_rpow_Ioi_of_exponent_nonpos hσ).mono him)).symm

section PowersOfOneFamily

variable {y : ι → ℝ} {lo hi u v m₁ M₁ m₂ M₂ : ℝ}

/-- `S u = ∑ i ∈ s, w i * (y i ^ (u / 2)) ^ 2` for a positive family `y`. -/
private lemma sum_mul_rpow_eq_sum_mul_sq (hy : ∀ i ∈ s, 0 < y i) (u : ℝ) :
    ∑ i ∈ s, w i * y i ^ u = ∑ i ∈ s, w i * (y i ^ (u / 2)) ^ 2 :=
  sum_congr rfl fun i hi ↦ by rw [← rpow_mul_natCast (hy i hi).le]; norm_num

/-- `S ((u + v) / 2) = ∑ i ∈ s, w i * (y i ^ (u / 2) * y i ^ (v / 2))` for a positive family `y`. -/
private lemma sum_mul_rpow_add_div_two (hy : ∀ i ∈ s, 0 < y i) (u v : ℝ) :
    ∑ i ∈ s, w i * y i ^ ((u + v) / 2) = ∑ i ∈ s, w i * (y i ^ (u / 2) * y i ^ (v / 2)) :=
  sum_congr rfl fun i hi ↦ by rw [← rpow_add (hy i hi), add_div]

/-- The case `σ ≥ 0 ≥ τ` of `Real.ozeki_rpow`. -/
private lemma four_mul_ozeki_rpow_of_nonneg_of_nonpos {σ τ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hy : ∀ i ∈ s, y i ∈ Set.Icc lo hi) (hσ : 0 ≤ σ)
    (hτ : τ ≤ 0) :
    4 * ((∑ i ∈ s, w i * (y i ^ σ) ^ 2) * (∑ i ∈ s, w i * (y i ^ τ) ^ 2) -
        (∑ i ∈ s, w i * (y i ^ σ * y i ^ τ)) ^ 2) ≤
      (∑ i ∈ s, w i) ^ 2 * (hi ^ σ * lo ^ τ - lo ^ σ * hi ^ τ) ^ 2 := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  have h1 := rpow_le_rpow hlo.le hlohi hσ
  have h2 := rpow_le_rpow_of_nonpos hlo hlohi hτ
  refine four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_mul_add_mul_le hw (rpow_pos_of_pos hlo σ)
    (rpow_pos_of_pos hhi τ)
    (fun i his ↦ ⟨rpow_le_rpow hlo.le (hy i his).1 hσ,
      rpow_le_rpow (hlo.le.trans (hy i his).1) (hy i his).2 hσ⟩)
    (fun i his ↦ ⟨rpow_le_rpow_of_nonpos (hlo.trans_le (hy i his).1) (hy i his).2 hτ,
      rpow_le_rpow_of_nonpos hlo (hy i his).1 hτ⟩) ?_
  -- the line condition, by convexity of `t ↦ c₁ * exp (σ * t) + c₂ * exp (τ * t)`
  have hf : ConvexOn ℝ Set.univ fun t : ℝ ↦ (lo ^ τ - hi ^ τ) • exp σ ^ t +
      (hi ^ σ - lo ^ σ) • exp τ ^ t :=
    ((convexOn_rpow_left (exp_pos σ)).smul (sub_nonneg.2 h2)).add
      ((convexOn_rpow_left (exp_pos τ)).smul (sub_nonneg.2 h1))
  have hev (z : ℝ) (hz : 0 < z) : (lo ^ τ - hi ^ τ) • exp σ ^ log z +
      (hi ^ σ - lo ^ σ) • exp τ ^ log z = (lo ^ τ - hi ^ τ) * z ^ σ +
      (hi ^ σ - lo ^ σ) * z ^ τ := by
    simp only [smul_eq_mul, ← exp_mul, rpow_def_of_pos hz, mul_comm σ, mul_comm τ]
  intro i his
  have hyi : 0 < y i := hlo.trans_le (hy i his).1
  have hmem : log (y i) ∈ segment ℝ (log lo) (log hi) := by
    rw [segment_eq_Icc (log_le_log hlo hlohi)]
    exact ⟨log_le_log hlo (hy i his).1, log_le_log hyi (hy i his).2⟩
  have := hf.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hmem
  rw [hev _ hyi, hev _ hlo, hev _ hhi] at this
  refine this.trans (max_le (le_of_eq ?_) (le_of_eq ?_)) <;> ring

/-- Ozeki's bound for the powers `y ^ σ`, `y ^ τ` of one family, in division-free form. -/
private lemma four_mul_ozeki_rpow {σ τ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hlo : 0 < lo)
    (hy : ∀ i ∈ s, y i ∈ Set.Icc lo hi) :
    4 * ((∑ i ∈ s, w i * (y i ^ σ) ^ 2) * (∑ i ∈ s, w i * (y i ^ τ) ^ 2) -
        (∑ i ∈ s, w i * (y i ^ σ * y i ^ τ)) ^ 2) ≤
      (∑ i ∈ s, w i) ^ 2 *
        (max (lo ^ σ) (hi ^ σ) * max (lo ^ τ) (hi ^ τ) -
          min (lo ^ σ) (hi ^ σ) * min (lo ^ τ) (hi ^ τ)) ^ 2 := by
  obtain rfl | ⟨i₀, hi₀⟩ := s.eq_empty_or_nonempty
  · simp
  have hlohi : lo ≤ hi := (hy i₀ hi₀).1.trans (hy i₀ hi₀).2
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hmem (e : ℝ) (i : ι) (his : i ∈ s) :
      y i ^ e ∈ Set.Icc (min (lo ^ e) (hi ^ e)) (max (lo ^ e) (hi ^ e)) := by
    rw [Set.Icc_min_max]
    exact rpow_mem_uIcc e hlo hhi (Set.Icc_subset_uIcc (hy i his))
  have hmono (h : 0 ≤ σ * τ) :=
    four_mul_sum_mul_sq_mul_sum_mul_sq_sub_sq_le_of_monovaryOn hw
      (le_min (rpow_nonneg hlo.le σ) (rpow_nonneg hhi.le σ))
      (le_min (rpow_nonneg hlo.le τ) (rpow_nonneg hhi.le τ)) (hmem σ) (hmem τ)
      (monovaryOn_rpow_rpow (fun i his ↦ hlo.trans_le (hy i his).1) h)
  obtain hσ | hσ := le_total 0 σ <;> obtain hτ | hτ := le_total 0 τ
  · exact hmono (mul_nonneg hσ hτ)
  · have h1 := rpow_le_rpow hlo.le hlohi hσ
    have h2 := rpow_le_rpow_of_nonpos hlo hlohi hτ
    rw [max_eq_right h1, min_eq_left h1, max_eq_left h2, min_eq_right h2]
    exact four_mul_ozeki_rpow_of_nonneg_of_nonpos s hw hlo hlohi hy hσ hτ
  · have h1 := rpow_le_rpow_of_nonpos hlo hlohi hσ
    have h2 := rpow_le_rpow hlo.le hlohi hτ
    rw [max_eq_left h1, min_eq_right h1, max_eq_right h2, min_eq_left h2]
    have := four_mul_ozeki_rpow_of_nonneg_of_nonpos s hw hlo hlohi hy hτ hσ
    have e : ∑ i ∈ s, w i * (y i ^ τ * y i ^ σ) = ∑ i ∈ s, w i * (y i ^ σ * y i ^ τ) :=
      sum_congr rfl fun i _ ↦ by rw [mul_comm (y i ^ τ)]
    rw [e] at this
    linear_combination this
  · exact hmono (mul_nonneg_of_nonpos_of_nonpos hσ hτ)

/-- **Cauchy–Schwarz inequality for powers of one family**: if `w i ≥ 0` and `y i > 0`, then
`S ((u + v) / 2) ^ 2 ≤ S u * S v`, where `S γ = ∑ i ∈ s, w i * y i ^ γ`. -/
theorem sq_sum_mul_rpow_add_div_two_le (hw : ∀ i ∈ s, 0 ≤ w i) (hy : ∀ i ∈ s, 0 < y i) :
    (∑ i ∈ s, w i * y i ^ ((u + v) / 2)) ^ 2 ≤
      (∑ i ∈ s, w i * y i ^ u) * ∑ i ∈ s, w i * y i ^ v := by
  rw [sum_mul_rpow_eq_sum_mul_sq s hy u, sum_mul_rpow_eq_sum_mul_sq s hy v,
    sum_mul_rpow_add_div_two s hy]
  exact sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _)) fun i _ ↦ le_of_eq (by ring)

/-- **Pólya–Szegő inequality for powers of one family**: if `w i ≥ 0`, `y i > 0`,
`y i ^ (u / 2) ∈ [m₁, M₁]` and `y i ^ (v / 2) ∈ [m₂, M₂]` with `0 < m₁`, `0 < m₂`, then
`S u * S v ≤ (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 * S ((u + v) / 2) ^ 2`,
where `S γ = ∑ i ∈ s, w i * y i ^ γ`. -/
theorem polya_szego_rpow (hw : ∀ i ∈ s, 0 ≤ w i) (hy : ∀ i ∈ s, 0 < y i) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (ha : ∀ i ∈ s, y i ^ (u / 2) ∈ Set.Icc m₁ M₁)
    (hb : ∀ i ∈ s, y i ^ (v / 2) ∈ Set.Icc m₂ M₂) :
    (∑ i ∈ s, w i * y i ^ u) * (∑ i ∈ s, w i * y i ^ v) ≤
      (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 *
        (∑ i ∈ s, w i * y i ^ ((u + v) / 2)) ^ 2 := by
  rw [sum_mul_rpow_eq_sum_mul_sq s hy u, sum_mul_rpow_eq_sum_mul_sq s hy v,
    sum_mul_rpow_add_div_two s hy]
  exact polya_szego s hw hm₁ hm₂ ha hb

/-- **Shisha–Mond inequality for powers of one family**: if `w i ≥ 0`, `y i > 0`,
`y i ^ (u / 2) ∈ [m₁, M₁]` and `y i ^ (v / 2) ∈ [m₂, M₂]` with `0 ≤ m₁`, `0 < m₂`, then
`S u / S ((u + v) / 2) - S ((u + v) / 2) / S v ≤ (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2`, where
`S γ = ∑ i ∈ s, w i * y i ^ γ`. -/
theorem shisha_mond_rpow (hw : ∀ i ∈ s, 0 ≤ w i) (hy : ∀ i ∈ s, 0 < y i) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 < m₂) (ha : ∀ i ∈ s, y i ^ (u / 2) ∈ Set.Icc m₁ M₁)
    (hb : ∀ i ∈ s, y i ^ (v / 2) ∈ Set.Icc m₂ M₂) :
    (∑ i ∈ s, w i * y i ^ u) / (∑ i ∈ s, w i * y i ^ ((u + v) / 2)) -
        (∑ i ∈ s, w i * y i ^ ((u + v) / 2)) / (∑ i ∈ s, w i * y i ^ v) ≤
      (√(M₁ / m₂) - √(m₁ / M₂)) ^ 2 := by
  obtain rfl | ⟨i₀, hi₀⟩ := s.eq_empty_or_nonempty
  · simpa using sq_nonneg (√(M₁ / m₂) - √(m₁ / M₂))
  have hM₁ : 0 ≤ M₁ := hm₁.trans ((ha i₀ hi₀).1.trans (ha i₀ hi₀).2)
  have hM₂ : 0 < M₂ := hm₂.trans_le ((hb i₀ hi₀).1.trans (hb i₀ hi₀).2)
  rw [sum_mul_rpow_eq_sum_mul_sq s hy u, sum_mul_rpow_eq_sum_mul_sq s hy v,
    sum_mul_rpow_add_div_two s hy]
  exact shisha_mond s hw (div_nonneg hm₁ hM₂.le) (div_nonneg hM₁ hm₂.le)
    (fun i hi ↦ div_mul_le_of_le_of_le hm₁ hM₂.le (ha i hi).1 (hb i hi).2)
    fun i hi ↦ le_div_mul_of_le_of_le hM₁ hm₂ (ha i hi).2 (hb i hi).1

/-- **Ozeki's inequality for powers of one family**: if `w i ≥ 0` and `0 < lo ≤ y i ≤ hi`, then
`S u * S v - S ((u + v) / 2) ^ 2 ≤ W ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2`, where
`S γ = ∑ i ∈ s, w i * y i ^ γ`, `W = ∑ i ∈ s, w i`, `m₁`, `M₁` are the smaller and the larger of
`lo ^ (u / 2)`, `hi ^ (u / 2)`, and `m₂`, `M₂` those of `lo ^ (v / 2)`, `hi ^ (v / 2)`. For
arbitrary families this bound fails, see `Counterexamples/Ozeki.lean`. -/
theorem ozeki_rpow (hw : ∀ i ∈ s, 0 ≤ w i) (hlo : 0 < lo) (hy : ∀ i ∈ s, y i ∈ Set.Icc lo hi) :
    (∑ i ∈ s, w i * y i ^ u) * (∑ i ∈ s, w i * y i ^ v) -
        (∑ i ∈ s, w i * y i ^ ((u + v) / 2)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ (u / 2)) (hi ^ (u / 2)) * max (lo ^ (v / 2)) (hi ^ (v / 2)) -
          min (lo ^ (u / 2)) (hi ^ (u / 2)) * min (lo ^ (v / 2)) (hi ^ (v / 2))) ^ 2 := by
  have hy' : ∀ i ∈ s, 0 < y i := fun i his ↦ hlo.trans_le (hy i his).1
  rw [sum_mul_rpow_eq_sum_mul_sq s hy' u, sum_mul_rpow_eq_sum_mul_sq s hy' v,
    sum_mul_rpow_add_div_two s hy']
  linarith [four_mul_ozeki_rpow s (σ := u / 2) (τ := v / 2) hw hlo hy]

/-- **Ozeki's inequality for powers of one family is sharp**: in `Real.ozeki_rpow` take `u = 2`,
`v = -2` (so `y ^ (u / 2) = y` and `y ^ (v / 2) = y⁻¹`), `0 < lo < hi`, and let every `y i` be `lo`
or `hi`, the indices with `y i = lo` having total weight `W / 2`, where `W = ∑ i ∈ s, w i` (so the
indices with `y i = hi` have total weight `W / 2` too). Then both sides of `Real.ozeki_rpow` are
equal, to `W ^ 2 * (hi ^ 2 - lo ^ 2) ^ 2 / (4 * lo ^ 2 * hi ^ 2)`. -/
theorem ozeki_rpow_eq (hu : u = 2) (hv : v = -2) (hlo : 0 < lo) (hlohi : lo < hi)
    (hy : ∀ i ∈ s, y i = lo ∨ y i = hi) (hW : ∑ i ∈ s with y i = lo, w i = (∑ i ∈ s, w i) / 2) :
    (∑ i ∈ s, w i * y i ^ u) * (∑ i ∈ s, w i * y i ^ v) -
        (∑ i ∈ s, w i * y i ^ ((u + v) / 2)) ^ 2 =
      (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ (u / 2)) (hi ^ (u / 2)) * max (lo ^ (v / 2)) (hi ^ (v / 2)) -
          min (lo ^ (u / 2)) (hi ^ (u / 2)) * min (lo ^ (v / 2)) (hi ^ (v / 2))) ^ 2 ∧
    (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ (u / 2)) (hi ^ (u / 2)) * max (lo ^ (v / 2)) (hi ^ (v / 2)) -
          min (lo ^ (u / 2)) (hi ^ (u / 2)) * min (lo ^ (v / 2)) (hi ^ (v / 2))) ^ 2 =
      (∑ i ∈ s, w i) ^ 2 * (hi ^ 2 - lo ^ 2) ^ 2 / (4 * lo ^ 2 * hi ^ 2) := by
  classical
  subst hu hv
  have hhi : 0 < hi := hlo.trans hlohi
  -- split every sum into the indices with `y i = lo` and those with `y i = hi`
  have hsplit (γ : ℝ) : ∑ i ∈ s, w i * y i ^ γ =
      lo ^ γ * ∑ i ∈ s with y i = lo, w i + hi ^ γ * ∑ i ∈ s with ¬y i = lo, w i := by
    rw [← sum_filter_add_sum_filter_not s (y · = lo), mul_sum, mul_sum]
    congr 1
    · exact sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2, mul_comm]
    · refine sum_congr rfl fun i hi ↦ ?_
      obtain ⟨his, hne⟩ := mem_filter.1 hi
      rw [(hy i his).resolve_left hne, mul_comm]
  have hB : ∑ i ∈ s with ¬y i = lo, w i = (∑ i ∈ s, w i) / 2 := by
    linarith [sum_filter_add_sum_filter_not s (y · = lo) w]
  have hinv : hi⁻¹ ≤ lo⁻¹ := (inv_le_inv₀ hhi hlo).2 hlohi.le
  rw [hsplit, hsplit, hsplit, hB, hW, show (2 + -2 : ℝ) / 2 = 0 by norm_num,
    show (2 : ℝ) / 2 = 1 by norm_num, show (-2 : ℝ) / 2 = -1 by norm_num]
  simp only [rpow_zero, rpow_one, rpow_two, rpow_neg hlo.le, rpow_neg hhi.le]
  rw [max_eq_right hlohi.le, min_eq_left hlohi.le, max_eq_left hinv, min_eq_right hinv]
  constructor
  · field_simp
    ring
  · field_simp

/-- **Diaz–Metcalf inequality for powers of one family**: if `w i ≥ 0`, `y i > 0`,
`y i ^ (u / 2) ∈ [m₁, M₁]` and `y i ^ (v / 2) ∈ [m₂, M₂]` with `0 < m₁`, `0 ≤ m₂`, then
`S v + m₂ * M₂ / (M₁ * m₁) * S u ≤ (M₂ / m₁ + m₂ / M₁) * S ((u + v) / 2)`, where
`S γ = ∑ i ∈ s, w i * y i ^ γ`. -/
theorem diaz_metcalf_rpow (hw : ∀ i ∈ s, 0 ≤ w i) (hy : ∀ i ∈ s, 0 < y i) (hm₁ : 0 < m₁)
    (hm₂ : 0 ≤ m₂) (ha : ∀ i ∈ s, y i ^ (u / 2) ∈ Set.Icc m₁ M₁)
    (hb : ∀ i ∈ s, y i ^ (v / 2) ∈ Set.Icc m₂ M₂) :
    ∑ i ∈ s, w i * y i ^ v + m₂ * M₂ / (M₁ * m₁) * ∑ i ∈ s, w i * y i ^ u ≤
      (M₂ / m₁ + m₂ / M₁) * ∑ i ∈ s, w i * y i ^ ((u + v) / 2) := by
  have h := diaz_metcalf hw
    (fun i hi ↦ div_mul_le_of_le_of_le hm₂ (hm₁.le.trans ((ha i hi).1.trans (ha i hi).2))
      (hb i hi).1 (ha i hi).2)
    fun i hi ↦ le_div_mul_of_le_of_le (hm₂.trans ((hb i hi).1.trans (hb i hi).2)) hm₁
      (hb i hi).2 (ha i hi).1
  rw [div_mul_div_comm, add_comm (m₂ / M₁)] at h
  rwa [sum_mul_rpow_eq_sum_mul_sq s hy u, sum_mul_rpow_eq_sum_mul_sq s hy v, add_comm u v,
    sum_mul_rpow_add_div_two s hy]

end PowersOfOneFamily

end Real
