/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Lagrange
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.MeanInequalities.Reverse
public import Mathlib.Analysis.Real.Sqrt

/-!
# Converse Hölder and converse Cauchy–Schwarz inequalities for weighted power sums

For weights `w i ≥ 0` and positive reals `x i`, `i ∈ s`, write `S γ = ∑ i ∈ s, w i * x i ^ γ` for
the weighted power sum of exponent `γ`, and `W = ∑ i ∈ s, w i`. Hölder's inequality bounds `S α`,
`α = u / p + v / q`, by `S u ^ (1 / p) * S v ^ (1 / q)`; this file bounds it from the other side
when the ratios `x i ^ ((u - v) / p)` lie in an interval `[m, M]`.

## Main results

* `Real.converse_holder_linear_of_one_lt`, `Real.converse_holder_linear_of_lt_one`: if
  `x i ^ ((u - v) / p) ∈ [m, M]` with `0 ≤ m`, then
  `(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * S α` for conjugate exponents
  `p`, `q` with `p > 1`, and the reverse inequality for `0 < p < 1`.
* `Real.converse_holder_of_one_lt`, `Real.converse_holder_of_lt_one`: if moreover `0 < m < M`,
  then `S u ^ (1 / p) * S v ^ (1 / q) ≤ λ * S α` for `p > 1`, and the reverse inequality for
  `0 < p < 1`, where
  `λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`.
* `Real.shisha_mond`: if `r * b i ≤ a i ≤ R * b i` with `0 ≤ r`, `0 ≤ R`, then
  `∑ w a ^ 2 / ∑ w a b - ∑ w a b / ∑ w b ^ 2 ≤ (√R - √r) ^ 2`.
* `Real.rpow_mem_Icc_min_max`: if `0 < lo ≤ y ≤ hi`, then `y ^ e` lies between `lo ^ e` and
  `hi ^ e`.
* `Real.ozeki_rpow`: Ozeki's bound for powers of one family: if `0 < lo ≤ y i ≤ hi`, then
  `(∑ w (y ^ σ) ^ 2) * (∑ w (y ^ τ) ^ 2) - (∑ w y ^ σ y ^ τ) ^ 2 ≤ W ^ 2 / 4 * (M₁ M₂ - m₁ m₂) ^ 2`,
  where `[m₁, M₁]` is the interval between `lo ^ σ` and `hi ^ σ`, and `[m₂, M₂]` the one between
  `lo ^ τ` and `hi ^ τ`.

Dujella, Jakšetić and Pečarić apply these inequalities in the unweighted case `w = 1` (their
Theorems 8 and 9). The Diaz–Metcalf and Pólya–Szegő inequalities and the Lagrange–Popoviciu bound,
which hold in any linearly ordered field, are in `Mathlib.Algebra.Order.BigOperators.Ring.Lagrange`.

## Implementation notes

Ozeki's inequality is often quoted for arbitrary families `m₁ ≤ a i ≤ M₁`, `m₂ ≤ b i ≤ M₂` of `n`
positive reals with the constant `n ^ 2 / 4`. In this form it is false: Izumino and Seo, and
Izumino, Mori and Seo, observed this and showed that the sharp constant for arbitrary families is
`n ^ 2 / 3` (see `Counterexamples/Ozeki.lean` for a three-term example). The constant `n ^ 2 / 4`
does hold when `a i = y i ^ σ` and `b i = y i ^ τ` are powers of one family (`Real.ozeki_rpow`).
If `σ` and `τ` have the same sign, then `a` and `b` monovary (`Finset.gram_le_of_monovaryOn`); if
they have opposite signs, then the points `(a i, b i)` lie below the line through the extreme
points, by convexity of `t ↦ A * exp (σ * t) + B * exp (τ * t)` for `A, B ≥ 0`
(`Finset.gram_le_of_mul_add_mul_le`).

## References

* [A. Dujella, J. Jakšetić and J. Pečarić, *Fibonacci numbers and Hölder inequality*]
  [dujella_jaksetic_pecaric]
* [O. Shisha and B. Mond, *Bounds on differences of means*][shisha_mond_1967]
* [N. Ozeki, *On the estimation of the inequalities by the maximum, or minimum values*]
  [ozeki_1968]
* [S. Izumino and Y. Seo, *On Ozeki's inequality and noncommutative covariance*]
  [izumino_seo_1997]
* [S. Izumino, H. Mori and Y. Seo, *On Ozeki's inequality*][izumino_mori_seo_1998]
-/

public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-! ### Converse Hölder -/

/-- The exponent bookkeeping behind the converse Hölder inequalities: with `r = y ^ ((u - v) / p)`,
`y ^ u = y ^ v * r ^ p` and `y ^ (u / p + v / q) = y ^ v * r`. -/
private lemma rpow_eq_rpow_mul_rpow {p q u v α y : ℝ} (hp : p ≠ 0) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hy : 0 < y) :
    y ^ u = y ^ v * (y ^ ((u - v) / p)) ^ p ∧ y ^ α = y ^ v * y ^ ((u - v) / p) := by
  have hαe : α = v + (u - v) / p := by
    rw [← hα, div_eq_mul_inv v q, show q⁻¹ = 1 - p⁻¹ by linarith]; ring
  refine ⟨?_, by rw [hαe, rpow_add hy]⟩
  rw [← rpow_mul hy.le, div_mul_cancel₀ _ hp, ← rpow_add hy, add_sub_cancel]

/-- **Linear converse Hölder inequality**, `p > 1`: for conjugate exponents `p`, `q`,
`α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 ≤ m`,
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * S α`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem converse_holder_linear_of_one_lt {p q u v α m M : ℝ} (hpq : p.HolderConjugate q)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 ≤ m)
    (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v ≤
      (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α := by
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  obtain ⟨hu, hα'⟩ := rpow_eq_rpow_mul_rpow hpq.ne_zero hpq.inv_add_inv_eq_one hα (hx i hi)
  obtain ⟨hmr, hrM⟩ := hr i hi
  -- the chord of the convex function `r ↦ r ^ p` over `[m, M]` lies above its graph
  have hc : (M - m) * (x i ^ ((u - v) / p)) ^ p ≤
      (M - x i ^ ((u - v) / p)) * m ^ p + (x i ^ ((u - v) / p) - m) * M ^ p := by
    obtain hmr | hmr := hmr.eq_or_lt
    · simp [← hmr]
    obtain hrM | hrM := hrM.eq_or_lt
    · simp [hrM]
    exact (convexOn_rpow hpq.lt.le).secant_mono_aux1 hm (hm.trans (hmr.trans hrM).le) hmr hrM
  have := mul_le_mul_of_nonneg_left hc (mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le v))
  rw [hu, hα']
  linarith

/-- **Linear converse Hölder inequality**, `0 < p < 1`: for `p⁻¹ + q⁻¹ = 1`,
`α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 ≤ m`,
`(M ^ p - m ^ p) * S α ≤ (M - m) * S u + (m * M ^ p - M * m ^ p) * S v`, where
`S γ = ∑ i ∈ s, w i * x i ^ γ`. -/
theorem converse_holder_linear_of_lt_one {p q u v α m M : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 ≤ m) (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α ≤
      (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v := by
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  obtain ⟨hu, hα'⟩ := rpow_eq_rpow_mul_rpow hp0.ne' hpq hα (hx i hi)
  obtain ⟨hmr, hrM⟩ := hr i hi
  -- the chord of the concave function `r ↦ r ^ p` over `[m, M]` lies below its graph
  have hc : (M - x i ^ ((u - v) / p)) * m ^ p + (x i ^ ((u - v) / p) - m) * M ^ p ≤
      (M - m) * (x i ^ ((u - v) / p)) ^ p := by
    obtain hmr | hmr := hmr.eq_or_lt
    · simp [← hmr]
    obtain hrM | hrM := hrM.eq_or_lt
    · simp [hrM]
    have := (concaveOn_rpow hp0.le hp1.le).neg.secant_mono_aux1 hm (hm.trans (hmr.trans hrM).le)
      hmr hrM
    simp only [Pi.neg_apply] at this
    linarith
  have := mul_le_mul_of_nonneg_left hc (mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le v))
  rw [hu, hα']
  linarith

/-- **Converse Hölder inequality**, `p > 1`: for conjugate exponents `p`, `q`,
`α = u / p + v / q`, `w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 < m < M`,
`S u ^ (1 / p) * S v ^ (1 / q) ≤ λ * S α`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`. -/
theorem converse_holder_of_one_lt {p q u v α m M : ℝ} (hpq : p.HolderConjugate q)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hmM : m < M) (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hM : 0 < M := hm.trans hmM
  have hA : 0 < p * (M - m) := mul_pos hp (sub_pos.2 hmM)
  have hB : 0 < q * (m * M ^ p - M * m ^ p) := by
    have h1 : m ^ (p - 1) < M ^ (p - 1) := rpow_lt_rpow hm.le hmM (sub_pos.2 hpq.lt)
    rw [rpow_sub_one hm.ne', rpow_sub_one hM.ne', div_lt_div_iff₀ hm hM] at h1
    nlinarith
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ s, w i * x i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  have hlin := converse_holder_linear_of_one_lt s hpq hα hw hx hm.le hr
  -- weighted AM-GM with weights `1 / p`, `1 / q`
  have hamgm := geom_mean_le_arith_mean2_weighted (by positivity : 0 ≤ 1 / p)
    (by positivity : 0 ≤ 1 / q) (mul_nonneg hA.le (hS u)) (mul_nonneg hB.le (hS v))
    (by simpa only [one_div] using hpq.inv_add_inv_eq_one)
  rw [mul_rpow hA.le (hS u), mul_rpow hB.le (hS v)] at hamgm
  have hK1 := rpow_pos_of_pos hA (1 / p)
  have hK2 := rpow_pos_of_pos hB (1 / q)
  rw [neg_div, neg_div, rpow_neg hA.le, rpow_neg hB.le]
  calc (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q)
      = (p * (M - m)) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) *
          ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q)) *
          ((p * (M - m)) ^ (1 / p))⁻¹ * ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q))⁻¹ := by
        field_simp
    _ ≤ (M ^ p - m ^ p) * (∑ i ∈ s, w i * x i ^ α) *
          ((p * (M - m)) ^ (1 / p))⁻¹ * ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q))⁻¹ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (hamgm.trans (le_of_eq_of_le ?_ hlin)) (inv_nonneg.2 hK1.le)) (inv_nonneg.2 hK2.le)
        field_simp
    _ = _ := by ring

/-- **Converse Hölder inequality**, `0 < p < 1`: for `p⁻¹ + q⁻¹ = 1`, `α = u / p + v / q`,
`w i ≥ 0`, `x i > 0` and `x i ^ ((u - v) / p) ∈ [m, M]` with `0 < m < M`,
`λ * S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`, where `S γ = ∑ i ∈ s, w i * x i ^ γ` and
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`.
Both `q` and `m * M ^ p - M * m ^ p` are negative here, so `λ` is positive. -/
theorem converse_holder_of_lt_one {p q u v α m M : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m) (hmM : m < M)
    (hr : ∀ i ∈ s, x i ^ ((u - v) / p) ∈ Set.Icc m M) :
    (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
  have hq := neg_of_inv_add_inv_eq_one hp0 hp1 hpq
  have hM : 0 < M := hm.trans hmM
  have hA : 0 < p * (M - m) := mul_pos hp0 (sub_pos.2 hmM)
  have hB : 0 < q * (m * M ^ p - M * m ^ p) := by
    have h1 : M ^ (p - 1) < m ^ (p - 1) := rpow_lt_rpow_of_neg hm hmM (by linarith)
    rw [rpow_sub_one hm.ne', rpow_sub_one hM.ne', div_lt_div_iff₀ hM hm] at h1
    nlinarith
  have hS (γ : ℝ) : 0 ≤ ∑ i ∈ s, w i * x i ^ γ :=
    sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  obtain hSv | hSv := (hS v).eq_or_lt
  · -- if `S v = 0`, then all weights vanish and both sides are zero
    have hw0 : ∀ i ∈ s, w i = 0 := fun i hi ↦ (mul_eq_zero.1 ((sum_eq_zero_iff_of_nonneg
      fun j hj ↦ mul_nonneg (hw j hj) (rpow_nonneg (hx j hj).le v)).1 hSv.symm i hi)).resolve_right
      (rpow_pos_of_pos (hx i hi) v).ne'
    rw [sum_eq_zero fun i hi ↦ by rw [hw0 i hi, zero_mul], ← hSv,
      zero_rpow (one_div_ne_zero hq.ne), mul_zero, mul_zero]
  have hlin := converse_holder_linear_of_lt_one s hp0 hp1 hpq hα hw hx hm.le hr
  have hy := young_inequality_of_lt_one (mul_nonneg hA.le (hS u)) (mul_pos hB hSv) hp0 hp1 hpq
  rw [mul_rpow hA.le (hS u), mul_rpow hB.le hSv.le] at hy
  have hK1 := rpow_pos_of_pos hA (1 / p)
  have hK2 := rpow_pos_of_pos hB (1 / q)
  rw [neg_div, neg_div, rpow_neg hA.le, rpow_neg hB.le]
  calc (M ^ p - m ^ p) * ((p * (M - m)) ^ (1 / p))⁻¹ *
        ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q))⁻¹ * ∑ i ∈ s, w i * x i ^ α
      = (M ^ p - m ^ p) * (∑ i ∈ s, w i * x i ^ α) *
          ((p * (M - m)) ^ (1 / p))⁻¹ * ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q))⁻¹ := by ring
    _ ≤ (p * (M - m)) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) *
          ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q)) *
          ((p * (M - m)) ^ (1 / p))⁻¹ * ((q * (m * M ^ p - M * m ^ p)) ^ (1 / q))⁻¹ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (hlin.trans (le_of_eq_of_le ?_ hy)) (inv_nonneg.2 hK1.le)) (inv_nonneg.2 hK2.le)
        field_simp [hq.ne]
    _ = (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
        field_simp

/-! ### Converse Cauchy–Schwarz -/

/-- **Shisha–Mond inequality**: if `w i ≥ 0`, `0 ≤ r`, `0 ≤ R`, `r * b i ≤ a i ≤ R * b i` and the
sums `∑ w a b`, `∑ w b ^ 2` are positive, then
`∑ w a ^ 2 / ∑ w a b - ∑ w a b / ∑ w b ^ 2 ≤ (√R - √r) ^ 2`. -/
theorem shisha_mond {a b : ι → ℝ} {r R : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hr0 : 0 ≤ r)
    (hR0 : 0 ≤ R) (hr : ∀ i ∈ s, r * b i ≤ a i) (hR : ∀ i ∈ s, a i ≤ R * b i)
    (hC : 0 < ∑ i ∈ s, w i * (a i * b i)) (hB : 0 < ∑ i ∈ s, w i * b i ^ 2) :
    (∑ i ∈ s, w i * a i ^ 2) / (∑ i ∈ s, w i * (a i * b i)) -
        (∑ i ∈ s, w i * (a i * b i)) / (∑ i ∈ s, w i * b i ^ 2) ≤
      (√R - √r) ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right (diaz_metcalf hw hr hR) hB.le
  rw [← sq_sqrt hr0, ← sq_sqrt hR0] at h1
  rw [div_sub_div _ _ hC.ne' hB.ne', div_le_iff₀ (mul_pos hC hB)]
  nlinarith [sq_nonneg (√r * √R * ∑ i ∈ s, w i * b i ^ 2 - ∑ i ∈ s, w i * (a i * b i))]

/-! ### Ozeki's inequality for powers of one family -/

/-- If `0 < lo ≤ y ≤ hi`, then `y ^ e` lies between `lo ^ e` and `hi ^ e`. -/
theorem rpow_mem_Icc_min_max {lo hi y : ℝ} (e : ℝ) (hlo : 0 < lo) (hy : y ∈ Set.Icc lo hi) :
    y ^ e ∈ Set.Icc (min (lo ^ e) (hi ^ e)) (max (lo ^ e) (hi ^ e)) := by
  obtain he | he := le_total 0 e
  · exact ⟨min_le_of_left_le (rpow_le_rpow hlo.le hy.1 he),
      le_max_of_le_right (rpow_le_rpow (hlo.le.trans hy.1) hy.2 he)⟩
  · exact ⟨min_le_of_right_le (rpow_le_rpow_of_nonpos (hlo.trans_le hy.1) hy.2 he),
      le_max_of_le_left (rpow_le_rpow_of_nonpos hlo hy.1 he)⟩

/-- Powers of one family with exponents of the same sign monovary. -/
private lemma monovaryOn_rpow {y : ι → ℝ} {σ τ : ℝ} (hy : ∀ i ∈ s, 0 < y i)
    (h : 0 ≤ σ ∧ 0 ≤ τ ∨ σ ≤ 0 ∧ τ ≤ 0) : MonovaryOn (y · ^ σ) (y · ^ τ) s := by
  refine monovaryOn_iff_forall_mul_nonneg.2 fun i hi j hj ↦ ?_
  obtain hij | hij := le_total (y i) (y j) <;> obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
  · exact mul_nonneg (sub_nonneg.2 (rpow_le_rpow (hy i hi).le hij h1))
      (sub_nonneg.2 (rpow_le_rpow (hy i hi).le hij h2))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (rpow_le_rpow_of_nonpos (hy i hi) hij h1))
      (sub_nonpos.2 (rpow_le_rpow_of_nonpos (hy i hi) hij h2))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (rpow_le_rpow (hy j hj).le hij h1))
      (sub_nonpos.2 (rpow_le_rpow (hy j hj).le hij h2))
  · exact mul_nonneg (sub_nonneg.2 (rpow_le_rpow_of_nonpos (hy j hj) hij h1))
      (sub_nonneg.2 (rpow_le_rpow_of_nonpos (hy j hj) hij h2))

/-- The case `σ ≥ 0 ≥ τ` of `Real.ozeki_rpow`. -/
private lemma ozeki_rpow_of_nonneg_of_nonpos {y : ι → ℝ} {lo hi σ τ : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlo : 0 < lo) (hlohi : lo ≤ hi) (hy : ∀ i ∈ s, y i ∈ Set.Icc lo hi)
    (hσ : 0 ≤ σ) (hτ : τ ≤ 0) :
    (∑ i ∈ s, w i * (y i ^ σ) ^ 2) * (∑ i ∈ s, w i * (y i ^ τ) ^ 2) -
        (∑ i ∈ s, w i * (y i ^ σ * y i ^ τ)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ σ) (hi ^ σ) * max (lo ^ τ) (hi ^ τ) -
          min (lo ^ σ) (hi ^ σ) * min (lo ^ τ) (hi ^ τ)) ^ 2 := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hyσ := fun i hi ↦ rpow_mem_Icc_min_max σ hlo (hy i hi)
  have hyτ := fun i hi ↦ rpow_mem_Icc_min_max τ hlo (hy i hi)
  have h1 := rpow_le_rpow hlo.le hlohi hσ
  have h2 := rpow_le_rpow_of_nonpos hlo hlohi hτ
  simp only [max_eq_right h1, min_eq_left h1, max_eq_left h2, min_eq_right h2] at hyσ hyτ ⊢
  refine gram_le_of_mul_add_mul_le hw (rpow_pos_of_pos hlo σ) (rpow_pos_of_pos hhi τ) hyσ hyτ ?_
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

/-- **Ozeki's inequality for powers of one family**: if `w i ≥ 0` and `0 < lo ≤ y i ≤ hi`, then
`(∑ w (y ^ σ) ^ 2) * (∑ w (y ^ τ) ^ 2) - (∑ w y ^ σ y ^ τ) ^ 2 ≤ W ^ 2 / 4 * (M₁ M₂ - m₁ m₂) ^ 2`,
where `W = ∑ i ∈ s, w i`, `m₁`, `M₁` are the smaller and the larger of `lo ^ σ`, `hi ^ σ`, and
`m₂`, `M₂` those of `lo ^ τ`, `hi ^ τ`. For arbitrary families this bound fails, see
`Counterexamples/Ozeki.lean`. -/
theorem ozeki_rpow {y : ι → ℝ} {lo hi σ τ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hlo : 0 < lo)
    (hy : ∀ i ∈ s, y i ∈ Set.Icc lo hi) :
    (∑ i ∈ s, w i * (y i ^ σ) ^ 2) * (∑ i ∈ s, w i * (y i ^ τ) ^ 2) -
        (∑ i ∈ s, w i * (y i ^ σ * y i ^ τ)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ σ) (hi ^ σ) * max (lo ^ τ) (hi ^ τ) -
          min (lo ^ σ) (hi ^ σ) * min (lo ^ τ) (hi ^ τ)) ^ 2 := by
  obtain rfl | ⟨i₀, hi₀⟩ := s.eq_empty_or_nonempty
  · simp
  have hlohi : lo ≤ hi := (hy i₀ hi₀).1.trans (hy i₀ hi₀).2
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hmono (h : 0 ≤ σ ∧ 0 ≤ τ ∨ σ ≤ 0 ∧ τ ≤ 0) := gram_le_of_monovaryOn hw
    (le_min (rpow_nonneg hlo.le σ) (rpow_nonneg hhi.le σ))
    (le_min (rpow_nonneg hlo.le τ) (rpow_nonneg hhi.le τ))
    (fun i hi ↦ rpow_mem_Icc_min_max σ hlo (hy i hi))
    (fun i hi ↦ rpow_mem_Icc_min_max τ hlo (hy i hi))
    (monovaryOn_rpow s (fun i hi ↦ hlo.trans_le (hy i hi).1) h)
  obtain hσ | hσ := le_total 0 σ <;> obtain hτ | hτ := le_total 0 τ
  · exact hmono (.inl ⟨hσ, hτ⟩)
  · exact ozeki_rpow_of_nonneg_of_nonpos s hw hlo hlohi hy hσ hτ
  · have := ozeki_rpow_of_nonneg_of_nonpos s hw hlo hlohi hy hτ hσ
    simp only [mul_comm (y _ ^ τ) (y _ ^ σ), mul_comm (max (lo ^ τ) (hi ^ τ)),
      mul_comm (min (lo ^ τ) (hi ^ τ))] at this
    linarith
  · exact hmono (.inr ⟨hσ, hτ⟩)

end Real
