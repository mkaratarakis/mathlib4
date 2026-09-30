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
  from ratio bounds `r * b i ≤ a i ≤ R * b i` with `0 < r` and `0 < R`, for arbitrary pairs.
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

private lemma rpow_chord_le {p m M r : ℝ} (hp : 1 ≤ p) (hm : 0 < m) (hmr : m ≤ r)
    (hrM : r ≤ M) : (M - m) * r ^ p ≤ (M - r) * m ^ p + (r - m) * M ^ p := by
  rcases hmr.eq_or_lt with rfl | hmr'
  · simp
  have hmM : 0 < M - m := by linarith
  have hne : M - m ≠ 0 := hmM.ne'
  have ha : 0 ≤ (M - r) / (M - m) := div_nonneg (by linarith) hmM.le
  have hb : 0 ≤ (r - m) / (M - m) := div_nonneg (by linarith) hmM.le
  have hab : (M - r) / (M - m) + (r - m) / (M - m) = 1 := by field_simp; ring
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 hm.le)
    (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ M)) ha hb hab
  have hr : (M - r) / (M - m) * m + (r - m) / (M - m) * M = r := by field_simp; ring
  simp only [smul_eq_mul, hr] at h
  calc (M - m) * r ^ p
      ≤ (M - m) * ((M - r) / (M - m) * m ^ p + (r - m) / (M - m) * M ^ p) := by gcongr
    _ = (M - r) * m ^ p + (r - m) * M ^ p := by field_simp

private lemma le_rpow_chord {p m M r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : 0 < m)
    (hmr : m ≤ r) (hrM : r ≤ M) : (M - r) * m ^ p + (r - m) * M ^ p ≤ (M - m) * r ^ p := by
  rcases hmr.eq_or_lt with rfl | hmr'
  · simp
  have hmM : 0 < M - m := by linarith
  have hne : M - m ≠ 0 := hmM.ne'
  have ha : 0 ≤ (M - r) / (M - m) := div_nonneg (by linarith) hmM.le
  have hb : 0 ≤ (r - m) / (M - m) := div_nonneg (by linarith) hmM.le
  have hab : (M - r) / (M - m) + (r - m) / (M - m) = 1 := by field_simp; ring
  have h := (concaveOn_rpow hp0 hp1).2 (Set.mem_Ici.2 hm.le)
    (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ M)) ha hb hab
  have hr : (M - r) / (M - m) * m + (r - m) / (M - m) * M = r := by field_simp; ring
  simp only [smul_eq_mul, hr] at h
  calc (M - r) * m ^ p + (r - m) * M ^ p
      = (M - m) * ((M - r) / (M - m) * m ^ p + (r - m) / (M - m) * M ^ p) := by field_simp
    _ ≤ (M - m) * r ^ p := by gcongr

private lemma holder_exps {p q u v α y : ℝ} (hp : p ≠ 0) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hy : 0 < y) :
    y ^ u = y ^ v * (y ^ ((u - v) / p)) ^ p ∧ y ^ α = y ^ v * y ^ ((u - v) / p) := by
  have hαe : α = v + (u - v) / p := by
    rw [← hα, div_eq_mul_inv v q, show q⁻¹ = 1 - p⁻¹ by linarith]; ring
  refine ⟨?_, ?_⟩
  · rw [← rpow_mul hy.le, div_mul_cancel₀ _ hp, ← rpow_add hy]; congr 1; ring
  · rw [hαe, rpow_add hy]

/-- **Reverse Young inequality**: for `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and `a, b > 0`,
`a / p + b / q ≤ a ^ (1 / p) * b ^ (1 / q)`. -/
private lemma reverse_young {p q a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpq : p⁻¹ + q⁻¹ = 1)
    (ha : 0 < a) (hb : 0 < b) : a / p + b / q ≤ a ^ (1 / p) * b ^ (1 / q) := by
  have hq : q⁻¹ = 1 - p⁻¹ := by linarith
  have hX : 0 < a ^ (1 / p) * b ^ (1 / q) := by positivity
  have h := geom_mean_le_arith_mean2_weighted hp0.le (by linarith : 0 ≤ 1 - p) hX.le hb.le
    (by ring)
  have hXp : (a ^ (1 / p) * b ^ (1 / q)) ^ p * b ^ (1 - p) = a := by
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul ha.le, ← rpow_mul hb.le, mul_assoc,
      ← rpow_add hb, one_div_mul_cancel hp0.ne', rpow_one]
    have : 1 / q * p + (1 - p) = 0 := by
      rw [one_div, hq]; field_simp; ring
    rw [this, rpow_zero, mul_one]
  rw [hXp] at h
  rw [div_eq_mul_inv b q, hq,
    show a / p + b * (1 - p⁻¹) = (a + b * (p - 1)) / p by field_simp,
    div_le_iff₀ hp0]
  linarith

/-- **Linear converse Hölder inequality**, `p > 1`: if `m ≤ x i ^ ((u - v) / p) ≤ M`, then
`(M - m) * S u + (m * M ^ p - M * m ^ p) * S v ≤ (M ^ p - m ^ p) * S α`. -/
theorem converse_holder_linear_of_one_lt {p q u v α m M : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v ≤
      (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α := by
  have hp0 : p ≠ 0 := (by linarith : 0 < p).ne'
  have key : ∀ i ∈ s, (M - m) * (w i * x i ^ u) + (m * M ^ p - M * m ^ p) * (w i * x i ^ v) ≤
      (M ^ p - m ^ p) * (w i * x i ^ α) := by
    intro i hi
    obtain ⟨hu, hα'⟩ := holder_exps hp0 hpq hα (hx i hi)
    have hc := rpow_chord_le hp.le hm (hr i hi).1 (hr i hi).2
    have hwx : 0 ≤ w i * x i ^ v := mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
    rw [hu, hα']
    have h2 := mul_le_mul_of_nonneg_left hc hwx
    linarith
  calc _ = ∑ i ∈ s, ((M - m) * (w i * x i ^ u) +
        (m * M ^ p - M * m ^ p) * (w i * x i ^ v)) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ ∑ i ∈ s, (M ^ p - m ^ p) * (w i * x i ^ α) := sum_le_sum key
    _ = _ := by rw [mul_sum]

/-- **Linear converse Hölder inequality**, `0 < p < 1`: the inequality of
`Real.converse_holder_linear_of_one_lt` reverses. -/
theorem converse_holder_linear_of_lt_one {p q u v α m M : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (M ^ p - m ^ p) * ∑ i ∈ s, w i * x i ^ α ≤
      (M - m) * ∑ i ∈ s, w i * x i ^ u + (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v := by
  have key : ∀ i ∈ s, (M ^ p - m ^ p) * (w i * x i ^ α) ≤
      (M - m) * (w i * x i ^ u) + (m * M ^ p - M * m ^ p) * (w i * x i ^ v) := by
    intro i hi
    obtain ⟨hu, hα'⟩ := holder_exps hp0.ne' hpq hα (hx i hi)
    have hc := le_rpow_chord hp0.le hp1.le hm (hr i hi).1 (hr i hi).2
    have hwx : 0 ≤ w i * x i ^ v := mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
    rw [hu, hα']
    have h2 := mul_le_mul_of_nonneg_left hc hwx
    linarith
  calc _ = ∑ i ∈ s, (M ^ p - m ^ p) * (w i * x i ^ α) := by rw [mul_sum]
    _ ≤ ∑ i ∈ s, ((M - m) * (w i * x i ^ u) +
        (m * M ^ p - M * m ^ p) * (w i * x i ^ v)) := sum_le_sum key
    _ = _ := by rw [sum_add_distrib, mul_sum, mul_sum]

/-- **Converse Hölder inequality**, `p > 1`: if `0 < m < M` and `m ≤ x i ^ ((u - v) / p) ≤ M`,
then `S u ^ (1 / p) * S v ^ (1 / q) ≤ λ * S α` with
`λ = (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q)`. -/
theorem converse_holder_of_one_lt {p q u v α m M : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) (hm : 0 < m)
    (hmM : m < M) (hr : ∀ i ∈ s, m ≤ x i ^ ((u - v) / p) ∧ x i ^ ((u - v) / p) ≤ M) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      (M ^ p - m ^ p) * (p * (M - m)) ^ (-1 / p) * (q * (m * M ^ p - M * m ^ p)) ^ (-1 / q) *
        ∑ i ∈ s, w i * x i ^ α := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    have h1 : q⁻¹ = 1 - p⁻¹ := by linarith
    have h2 : 0 < q⁻¹ := by rw [h1]; linarith [inv_lt_one_of_one_lt₀ hp]
    exact inv_pos.1 h2
  have hM : 0 < M := hm.trans hmM
  have hA : 0 < M - m := by linarith
  have hB : 0 < m * M ^ p - M * m ^ p := by
    have h1 : m ^ (p - 1) < M ^ (p - 1) := rpow_lt_rpow hm.le hmM (by linarith)
    rw [rpow_sub_one hm.ne', rpow_sub_one hM.ne', div_lt_div_iff₀ hm hM] at h1
    linarith
  have hSU : 0 ≤ ∑ i ∈ s, w i * x i ^ u :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  have hSV : 0 ≤ ∑ i ∈ s, w i * x i ^ v :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  have hlin := converse_holder_linear_of_one_lt s hp hpq hα hw hx hm hr
  have hpq' : 1 / p + 1 / q = 1 := by simpa [one_div] using hpq
  have hamgm := geom_mean_le_arith_mean2_weighted (by positivity : 0 ≤ 1 / p)
    (by positivity : 0 ≤ 1 / q) (by positivity : 0 ≤ p * (M - m) * ∑ i ∈ s, w i * x i ^ u)
    (by positivity : 0 ≤ q * (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v) hpq'
  rw [mul_rpow (by positivity) hSU, mul_rpow (by positivity) hSV] at hamgm
  have e1 : 1 / p * (p * (M - m) * ∑ i ∈ s, w i * x i ^ u) =
      (M - m) * ∑ i ∈ s, w i * x i ^ u := by field_simp
  have e2 : 1 / q * (q * (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v) =
      (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v := by field_simp
  rw [e1, e2] at hamgm
  rw [neg_div, neg_div, rpow_neg (by positivity), rpow_neg (by positivity)]
  have hK1 : 0 < (p * (M - m)) ^ (1 / p) := by positivity
  have hK2 : 0 < (q * (m * M ^ p - M * m ^ p)) ^ (1 / q) := by positivity
  rw [show ∀ K L T : ℝ, (M ^ p - m ^ p) * K⁻¹ * L⁻¹ * T = (M ^ p - m ^ p) * T / (K * L) by
    intros; field_simp, le_div_iff₀ (by positivity)]
  linarith

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
  have hq : q < 0 := by
    have h1 : q⁻¹ = 1 - p⁻¹ := by linarith
    have h2 : q⁻¹ < 0 := by rw [h1]; linarith [(one_lt_inv₀ hp0).2 hp1]
    exact inv_neg''.1 h2
  have hM : 0 < M := hm.trans hmM
  have hA : 0 < M - m := by linarith
  have hB : m * M ^ p - M * m ^ p < 0 := by
    have h1 : M ^ (p - 1) < m ^ (p - 1) := rpow_lt_rpow_of_neg hm hmM (by linarith)
    rw [rpow_sub_one hm.ne', rpow_sub_one hM.ne', div_lt_div_iff₀ hM hm] at h1
    linarith
  have hqB : 0 < q * (m * M ^ p - M * m ^ p) := mul_pos_of_neg_of_neg hq hB
  have hSU : 0 < ∑ i ∈ s, w i * x i ^ u :=
    sum_pos (fun i hi => mul_pos (hw i hi) (rpow_pos_of_pos (hx i hi) _)) hs
  have hSV : 0 < ∑ i ∈ s, w i * x i ^ v :=
    sum_pos (fun i hi => mul_pos (hw i hi) (rpow_pos_of_pos (hx i hi) _)) hs
  have hlin := converse_holder_linear_of_lt_one s hp0 hp1 hpq hα (fun i hi => (hw i hi).le) hx
    hm hr
  have hy := reverse_young hp0 hp1 hpq (by positivity : 0 < p * (M - m) * ∑ i ∈ s, w i * x i ^ u)
    (mul_pos hqB hSV)
  rw [mul_rpow (by positivity) hSU.le, mul_rpow hqB.le hSV.le] at hy
  have e1 : p * (M - m) * (∑ i ∈ s, w i * x i ^ u) / p =
      (M - m) * ∑ i ∈ s, w i * x i ^ u := by field_simp
  have e2 : q * (m * M ^ p - M * m ^ p) * (∑ i ∈ s, w i * x i ^ v) / q =
      (m * M ^ p - M * m ^ p) * ∑ i ∈ s, w i * x i ^ v := by
    have := hq.ne; field_simp
  rw [e1, e2] at hy
  rw [neg_div, neg_div, rpow_neg (by positivity), rpow_neg hqB.le]
  have hK1 : 0 < (p * (M - m)) ^ (1 / p) := by positivity
  have hK2 : 0 < (q * (m * M ^ p - M * m ^ p)) ^ (1 / q) := rpow_pos_of_pos hqB _
  rw [show ∀ K L T : ℝ, (M ^ p - m ^ p) * K⁻¹ * L⁻¹ * T = (M ^ p - m ^ p) * T / (K * L) by
    intros; field_simp, div_le_iff₀ (by positivity)]
  linarith

/-! ### Converse Cauchy inequalities from ratio bounds -/

variable {a b : ι → ℝ} {r R : ℝ}

/-- **Diaz–Metcalf inequality**: if `r * b i ≤ a i ≤ R * b i`, then
`∑ w a ^ 2 + r * R * ∑ w b ^ 2 ≤ (r + R) * ∑ w a b`. -/
theorem diaz_metcalf (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, r * b i ≤ a i)
    (hR : ∀ i ∈ s, a i ≤ R * b i) :
    ∑ i ∈ s, w i * a i ^ 2 + r * R * ∑ i ∈ s, w i * b i ^ 2 ≤
      (r + R) * ∑ i ∈ s, w i * (a i * b i) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i hi => ?_
  have h := mul_nonneg (hw i hi)
    (mul_nonneg (sub_nonneg.2 (hr i hi)) (sub_nonneg.2 (hR i hi)))
  linarith

/-- **Pólya–Szegő inequality**: if `0 < r`, `0 < R` and `r * b i ≤ a i ≤ R * b i`, then
`(∑ w a ^ 2) * (∑ w b ^ 2) ≤ (r + R) ^ 2 / (4 * r * R) * (∑ w a b) ^ 2`. -/
theorem polya_szego (hw : ∀ i ∈ s, 0 ≤ w i) (hr0 : 0 < r) (hR0 : 0 < R)
    (hr : ∀ i ∈ s, r * b i ≤ a i) (hR : ∀ i ∈ s, a i ≤ R * b i) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) ≤
      (r + R) ^ 2 / (4 * r * R) * (∑ i ∈ s, w i * (a i * b i)) ^ 2 := by
  have hdm := diaz_metcalf s hw hr hR
  have hA : 0 ≤ ∑ i ∈ s, w i * a i ^ 2 := sum_nonneg fun i hi => by have := hw i hi; positivity
  have hB : 0 ≤ ∑ i ∈ s, w i * b i ^ 2 := sum_nonneg fun i hi => by have := hw i hi; positivity
  have h0 : 0 ≤ ∑ i ∈ s, w i * a i ^ 2 + r * R * ∑ i ∈ s, w i * b i ^ 2 := by positivity
  have h1 := pow_le_pow_left₀ h0 hdm 2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (∑ i ∈ s, w i * a i ^ 2 - r * R * ∑ i ∈ s, w i * b i ^ 2)]

/-- **Shisha–Mond inequality**: if `0 < r`, `0 ≤ R`, `r * b i ≤ a i ≤ R * b i` and the sums
`∑ w a b`, `∑ w b ^ 2` are positive, then
`∑ w a ^ 2 / ∑ w a b - ∑ w a b / ∑ w b ^ 2 ≤ (√R - √r) ^ 2`. -/
theorem shisha_mond (hw : ∀ i ∈ s, 0 ≤ w i) (hr0 : 0 < r) (hR0 : 0 ≤ R)
    (hr : ∀ i ∈ s, r * b i ≤ a i) (hR : ∀ i ∈ s, a i ≤ R * b i)
    (hC : 0 < ∑ i ∈ s, w i * (a i * b i)) (hB : 0 < ∑ i ∈ s, w i * b i ^ 2) :
    (∑ i ∈ s, w i * a i ^ 2) / (∑ i ∈ s, w i * (a i * b i)) -
        (∑ i ∈ s, w i * (a i * b i)) / (∑ i ∈ s, w i * b i ^ 2) ≤
      (√R - √r) ^ 2 := by
  have hdm := diaz_metcalf s hw hr hR
  have hsr := sq_sqrt hr0.le
  have hsR := sq_sqrt hR0
  have h1 := mul_le_mul_of_nonneg_right hdm hB.le
  rw [← hsr, ← hsR] at h1
  rw [div_sub_div _ _ hC.ne' hB.ne', div_le_iff₀ (mul_pos hC hB)]
  nlinarith [sq_nonneg (√r * √R * ∑ i ∈ s, w i * b i ^ 2 - ∑ i ∈ s, w i * (a i * b i))]

/-! ### Ozeki-type bounds -/

/-- The weighted Lagrange identity. -/
private lemma lagrange_identity (a b : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 =
      2 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) -
        (∑ i ∈ s, w i * (a i * b i)) ^ 2) := by
  rw [show ∀ A B C : ℝ, 2 * (A * B - C ^ 2) = A * B + B * A - 2 * (C * C) by intros; ring,
    sum_mul_sum, sum_mul_sum, sum_mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

private lemma sq_sum_le_mul (a b : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (a i * b i)) ^ 2 ≤
      (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) := by
  have h := lagrange_identity s (w := w) a b
  have h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 :=
    sum_nonneg fun i hi => sum_nonneg fun j hj => by
      have := hw i hi; have := hw j hj; positivity
  linarith

/-- **Lagrange–Popoviciu bound**: if every Lagrange term `a i * b j - a j * b i` is dominated
by `c i - c j`, and `lo ≤ c i ≤ hi`, then
`(∑ w a ^ 2) * (∑ w b ^ 2) - (∑ w a b) ^ 2 ≤ (∑ w) ^ 2 * (hi - lo) ^ 2 / 4`. -/
theorem gram_le_of_sq_le {c : ι → ℝ} {lo hi : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hc : ∀ i ∈ s, lo ≤ c i ∧ c i ≤ hi)
    (hdom : ∀ i ∈ s, ∀ j ∈ s, (a i * b j - a j * b i) ^ 2 ≤ (c i - c j) ^ 2) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) - (∑ i ∈ s, w i * (a i * b i)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 * (hi - lo) ^ 2 / 4 := by
  have hL := lagrange_identity s (w := w) a b
  have hL' := lagrange_identity s (w := w) c (fun _ => 1)
  simp only [mul_one, one_pow] at hL'
  have hle : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 ≤
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (c i - c j) ^ 2 :=
    sum_le_sum fun i hi => sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hdom i hi j hj) (mul_nonneg (hw i hi) (hw j hj))
  have hW : 0 ≤ ∑ i ∈ s, w i := sum_nonneg hw
  have hpop : 0 ≤ ∑ i ∈ s, w i * ((c i - lo) * (hi - c i)) :=
    sum_nonneg fun i h => mul_nonneg (hw i h)
      (mul_nonneg (sub_nonneg.2 (hc i h).1) (sub_nonneg.2 (hc i h).2))
  have hpop' : ∑ i ∈ s, w i * ((c i - lo) * (hi - c i)) = (lo + hi) * ∑ i ∈ s, w i * c i -
      ∑ i ∈ s, w i * c i ^ 2 - lo * hi * ∑ i ∈ s, w i := by
    simp only [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hQ : ∑ i ∈ s, w i * c i ^ 2 ≤
      (lo + hi) * ∑ i ∈ s, w i * c i - lo * hi * ∑ i ∈ s, w i := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hQ hW,
    sq_nonneg (∑ i ∈ s, w i * c i - (∑ i ∈ s, w i) * (lo + hi) / 2)]

private lemma rpow_mem_min_max {lo hi y e : ℝ} (hlo : 0 < lo) (hy : lo ≤ y) (hyh : y ≤ hi) :
    min (lo ^ e) (hi ^ e) ≤ y ^ e ∧ y ^ e ≤ max (lo ^ e) (hi ^ e) := by
  rcases le_total 0 e with he | he
  · exact ⟨min_le_of_left_le (rpow_le_rpow hlo.le hy he),
      le_max_of_le_right (rpow_le_rpow (hlo.le.trans hy) hyh he)⟩
  · exact ⟨min_le_of_right_le (rpow_le_rpow_of_nonpos (hlo.trans_le hy) hyh he),
      le_max_of_le_left (rpow_le_rpow_of_nonpos hlo hy he)⟩

private lemma rpow_sub_mul_rpow_sub_nonneg {y z σ τ : ℝ} (hy : 0 < y) (hz : 0 < z)
    (h : 0 ≤ σ ∧ 0 ≤ τ ∨ σ ≤ 0 ∧ τ ≤ 0) : 0 ≤ (y ^ σ - z ^ σ) * (y ^ τ - z ^ τ) := by
  rcases le_total y z with hyz | hyz <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (rpow_le_rpow hy.le hyz h1))
      (sub_nonpos.2 (rpow_le_rpow hy.le hyz h2))
  · exact mul_nonneg (sub_nonneg.2 (rpow_le_rpow_of_nonpos hy hyz h1))
      (sub_nonneg.2 (rpow_le_rpow_of_nonpos hy hyz h2))
  · exact mul_nonneg (sub_nonneg.2 (rpow_le_rpow hz.le hyz h1))
      (sub_nonneg.2 (rpow_le_rpow hz.le hyz h2))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (rpow_le_rpow_of_nonpos hz hyz h1))
      (sub_nonpos.2 (rpow_le_rpow_of_nonpos hz hyz h2))

/-- Ozeki-type bound when `a` and `b` are similarly ordered. -/
private lemma gram_le_of_mono {m₁ M₁ m₂ M₂ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hm₁ : 0 ≤ m₁)
    (hm₂ : 0 ≤ m₂) (ha : ∀ i ∈ s, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i ∈ s, m₂ ≤ b i ∧ b i ≤ M₂)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (a i - a j) * (b i - b j)) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) - (∑ i ∈ s, w i * (a i * b i)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  refine (gram_le_of_sq_le s (c := fun i => a i * b i) (lo := m₁ * m₂) (hi := M₁ * M₂) hw
    (fun i hi => ⟨mul_le_mul (ha i hi).1 (hb i hi).1 hm₂ (hm₁.trans (ha i hi).1),
      mul_le_mul (ha i hi).2 (hb i hi).2 (hm₂.trans (hb i hi).1)
        (hm₁.trans ((ha i hi).1.trans (ha i hi).2))⟩) fun i hi j hj => ?_).trans_eq (by ring)
  have hai := hm₁.trans (ha i hi).1
  have haj := hm₁.trans (ha j hj).1
  have hbi := hm₂.trans (hb i hi).1
  have hbj := hm₂.trans (hb j hj).1
  have key : (a i * b i - a j * b j) ^ 2 - (a i * b j - a j * b i) ^ 2 =
      (a i + a j) * (b i + b j) * ((a i - a j) * (b i - b j)) := by ring
  have := mul_nonneg (mul_nonneg (add_nonneg hai haj) (add_nonneg hbi hbj)) (hmono i hi j hj)
  linarith

/-- Ozeki-type bound when the points `(a i, b i)` lie below the chord joining `(m₁, M₂)` and
`(M₁, m₂)`. -/
private lemma gram_le_of_chord {m₁ M₁ m₂ M₂ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (h₁ : m₁ ≤ M₁) (h₂ : m₂ ≤ M₂) (hD : 0 < M₁ * M₂ - m₁ * m₂)
    (ha : ∀ i ∈ s, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i ∈ s, m₂ ≤ b i ∧ b i ≤ M₂)
    (hchord : ∀ i ∈ s, (M₂ - m₂) * a i + (M₁ - m₁) * b i ≤ M₁ * M₂ - m₁ * m₂) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) - (∑ i ∈ s, w i * (a i * b i)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  have hN : ∀ i ∈ s, 0 < (M₂ - m₂) * a i + (M₁ - m₁) * b i := by
    intro i hi
    have hai := hm₁.trans_le (ha i hi).1
    have hbi := hm₂.trans_le (hb i hi).1
    rcases (sub_nonneg.2 h₂).eq_or_lt with h | h
    · have : 0 < M₁ - m₁ := by nlinarith
      rw [← h]; nlinarith
    · nlinarith [mul_pos h hai, mul_nonneg (sub_nonneg.2 h₁) hbi.le]
  refine (gram_le_of_sq_le s (c := fun i => (m₁ * b i - M₂ * a i) * (M₁ * M₂ - m₁ * m₂) /
    ((M₂ - m₂) * a i + (M₁ - m₁) * b i)) (lo := -(M₁ * M₂ - m₁ * m₂)) (hi := 0) hw
    (fun i hi => ?_) fun i hi j hj => ?_).trans_eq (by ring)
  · have hNi := hN i hi
    constructor
    · rw [le_div_iff₀ hNi]
      have h : 0 ≤ M₁ * b i - m₂ * a i := by
        nlinarith [mul_nonneg (hm₁.le.trans h₁) (sub_nonneg.2 (hb i hi).1),
          mul_nonneg hm₂.le (sub_nonneg.2 (ha i hi).2)]
      nlinarith [mul_nonneg hD.le h]
    · refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ?_ hD.le) hNi.le
      nlinarith [(ha i hi).1, (hb i hi).2]
  · have hNi := hN i hi
    have hNj := hN j hj
    have hNi' := hchord i hi
    have hNj' := hchord j hj
    have hNi0 := hNi.ne'
    have hNj0 := hNj.ne'
    have e : ∀ Ni Nj : ℝ, Ni = (M₂ - m₂) * a i + (M₁ - m₁) * b i →
        Nj = (M₂ - m₂) * a j + (M₁ - m₁) * b j → Ni ≠ 0 → Nj ≠ 0 →
        (m₁ * b i - M₂ * a i) * (M₁ * M₂ - m₁ * m₂) / Ni -
          (m₁ * b j - M₂ * a j) * (M₁ * M₂ - m₁ * m₂) / Nj =
          -((M₁ * M₂ - m₁ * m₂) ^ 2 / (Ni * Nj)) * (a i * b j - a j * b i) := by
      intro Ni Nj hi hj h0 h0'
      field_simp
      subst hi hj
      ring
    rw [e _ _ rfl rfl hNi0 hNj0, mul_pow, neg_sq]
    have hk : 1 ≤ (M₁ * M₂ - m₁ * m₂) ^ 2 / (((M₂ - m₂) * a i + (M₁ - m₁) * b i) *
          ((M₂ - m₂) * a j + (M₁ - m₁) * b j)) := by
      rw [le_div_iff₀ (mul_pos hNi hNj), one_mul, sq]
      exact mul_le_mul hNi' hNj' hNj.le hD.le
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hk)

/-- The case `σ > 0 > τ` of `Real.ozeki_rpow`. -/
private lemma ozeki_rpow_of_pos_of_neg {y : ι → ℝ} {lo hi σ τ : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hy : ∀ i ∈ s, lo ≤ y i ∧ y i ≤ hi) (hσ : 0 < σ)
    (hτ : τ < 0) :
    (∑ i ∈ s, w i * (y i ^ σ) ^ 2) * (∑ i ∈ s, w i * (y i ^ τ) ^ 2) -
        (∑ i ∈ s, w i * (y i ^ σ * y i ^ τ)) ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 / 4 *
        (max (lo ^ σ) (hi ^ σ) * max (lo ^ τ) (hi ^ τ) -
          min (lo ^ σ) (hi ^ σ) * min (lo ^ τ) (hi ^ τ)) ^ 2 := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hyσ := fun i hi => rpow_mem_min_max (e := σ) hlo (hy i hi).1 (hy i hi).2
  have hyτ := fun i hi => rpow_mem_min_max (e := τ) hlo (hy i hi).1 (hy i hi).2
  rcases hlohi.eq_or_lt with rfl | hlh
  · refine gram_le_of_mono s hw (by positivity) (by positivity) hyσ hyτ fun i hi j hj => ?_
    have : y i = y j := by linarith [hy i hi, hy j hj]
    rw [this]; simp
  simp only [max_eq_right (rpow_le_rpow hlo.le hlh.le hσ.le),
    min_eq_left (rpow_le_rpow hlo.le hlh.le hσ.le),
    max_eq_left (rpow_le_rpow_of_nonpos hlo hlh.le hτ.le),
    min_eq_right (rpow_le_rpow_of_nonpos hlo hlh.le hτ.le)] at hyσ hyτ ⊢
  have h1 : lo ^ σ < hi ^ σ := rpow_lt_rpow hlo.le hlh hσ
  have h2 : hi ^ τ < lo ^ τ := rpow_lt_rpow_of_neg hlo hlh hτ
  have hD : 0 < hi ^ σ * lo ^ τ - lo ^ σ * hi ^ τ := by
    have := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < hi ^ τ)
    have := mul_lt_mul_of_pos_left h2 (by positivity : (0 : ℝ) < hi ^ σ)
    linarith
  refine gram_le_of_chord s hw (by positivity) (by positivity) h1.le h2.le hD hyσ hyτ ?_
  -- the chord condition, by convexity of `t ↦ c₁ e ^ (σ t) + c₂ e ^ (τ t)`
  have hf : ConvexOn ℝ Set.univ fun t : ℝ => (lo ^ τ - hi ^ τ) • exp σ ^ t +
      (hi ^ σ - lo ^ σ) • exp τ ^ t :=
    ((convexOn_rpow_left (exp_pos σ)).smul (c := lo ^ τ - hi ^ τ) (by linarith)).add
      ((convexOn_rpow_left (exp_pos τ)).smul (c := hi ^ σ - lo ^ σ) (by linarith))
  have hev : ∀ z : ℝ, 0 < z → (lo ^ τ - hi ^ τ) • exp σ ^ log z +
      (hi ^ σ - lo ^ σ) • exp τ ^ log z = (lo ^ τ - hi ^ τ) * z ^ σ +
      (hi ^ σ - lo ^ σ) * z ^ τ := by
    intro z hz
    simp only [smul_eq_mul, ← exp_mul, rpow_def_of_pos hz, mul_comm σ, mul_comm τ]
  intro i his
  have hyi : 0 < y i := hlo.trans_le (hy i his).1
  have hmem : log (y i) ∈ segment ℝ (log lo) (log hi) := by
    rw [segment_eq_Icc (log_le_log hlo hlh.le)]
    exact ⟨log_le_log hlo (hy i his).1, log_le_log hyi (hy i his).2⟩
  have := hf.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hmem
  rw [hev _ hyi, hev _ hlo, hev _ hhi] at this
  have e1 : (lo ^ τ - hi ^ τ) * lo ^ σ + (hi ^ σ - lo ^ σ) * lo ^ τ =
      hi ^ σ * lo ^ τ - lo ^ σ * hi ^ τ := by ring
  have e2 : (lo ^ τ - hi ^ τ) * hi ^ σ + (hi ^ σ - lo ^ σ) * hi ^ τ =
      hi ^ σ * lo ^ τ - lo ^ σ * hi ^ τ := by ring
  rwa [e1, e2, max_self] at this

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
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  have hlohi : lo ≤ hi := (hy i₀ hi₀).1.trans (hy i₀ hi₀).2
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hcases : (0 ≤ σ ∧ 0 ≤ τ ∨ σ ≤ 0 ∧ τ ≤ 0) ∨ (0 < σ ∧ τ < 0) ∨ (σ < 0 ∧ 0 < τ) := by
    rcases le_or_gt 0 σ with h1 | h1 <;> rcases le_or_gt 0 τ with h2 | h2
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · rcases h1.eq_or_lt with h1 | h1
      · exact Or.inl (Or.inr ⟨h1.symm.le, h2.le⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rcases h2.eq_or_lt with h2 | h2
      · exact Or.inl (Or.inr ⟨h1.le, h2.symm.le⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inl (Or.inr ⟨h1.le, h2.le⟩)
  rcases hcases with h | h | h
  · exact gram_le_of_mono s hw (by positivity) (by positivity)
      (fun i hi => rpow_mem_min_max hlo (hy i hi).1 (hy i hi).2)
      (fun i hi => rpow_mem_min_max hlo (hy i hi).1 (hy i hi).2) fun i hi j hj =>
        rpow_sub_mul_rpow_sub_nonneg (hlo.trans_le (hy i hi).1) (hlo.trans_le (hy j hj).1) h
  · exact ozeki_rpow_of_pos_of_neg s hw hlo hlohi hy h.1 h.2
  · have := ozeki_rpow_of_pos_of_neg s hw hlo hlohi hy h.2 h.1
    simp only [mul_comm (y _ ^ τ) (y _ ^ σ), mul_comm (max (lo ^ τ) (hi ^ τ)),
      mul_comm (min (lo ^ τ) (hi ^ τ))] at this
    linarith

/-- **Ozeki's inequality fails for arbitrary tuples**: there are `a, b : Fin 3 → ℝ` with
`1 ≤ a i ≤ 10` and `1 ≤ b i ≤ 10` for which
`(∑ a ^ 2) * (∑ b ^ 2) - (∑ a b) ^ 2 > 3 ^ 2 / 4 * (10 * 10 - 1 * 1) ^ 2`. -/
theorem not_ozeki :
    ¬ ∀ (a b : Fin 3 → ℝ) (m₁ M₁ m₂ M₂ : ℝ), 0 < m₁ → 0 < m₂ →
      (∀ i, m₁ ≤ a i ∧ a i ≤ M₁) → (∀ i, m₂ ≤ b i ∧ b i ≤ M₂) →
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 ≤
        (3 : ℝ) ^ 2 / 4 * (M₁ * M₂ - m₁ * m₂) ^ 2 := by
  intro h
  have := h ![10, 10, 1] ![1, 10, 10] 1 10 1 10 one_pos one_pos
    (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
  simp only [Fin.sum_univ_three] at this
  norm_num at this

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
  obtain ⟨i₀, hi₀⟩ := hs
  have hlohi : lo ≤ hi := (hx i₀ hi₀).1.trans (hx i₀ hi₀).2
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hw' : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  have hxp : ∀ i ∈ s, 0 < x i := fun i hi => hlo.trans_le (hx i hi).1
  have hm₁0 : 0 < m₁ := hm₁ ▸ lt_min (by positivity) (by positivity)
  have hm₂0 : 0 < m₂ := hm₂ ▸ lt_min (by positivity) (by positivity)
  have hM₁0 : 0 < M₁ := hM₁ ▸ lt_max_of_lt_left (by positivity)
  have hM₂0 : 0 < M₂ := hM₂ ▸ lt_max_of_lt_left (by positivity)
  have ha : ∀ i ∈ s, m₁ ≤ x i ^ (u / 2) ∧ x i ^ (u / 2) ≤ M₁ := fun i hi =>
    hm₁ ▸ hM₁ ▸ rpow_mem_min_max hlo (hx i hi).1 (hx i hi).2
  have hb : ∀ i ∈ s, m₂ ≤ x i ^ (v / 2) ∧ x i ^ (v / 2) ≤ M₂ := fun i hi =>
    hm₂ ▸ hM₂ ▸ rpow_mem_min_max hlo (hx i hi).1 (hx i hi).2
  have hsq : ∀ e : ℝ, ∀ i ∈ s, (x i ^ (e / 2)) ^ 2 = x i ^ e := fun e i hi => by
    rw [← rpow_natCast, ← rpow_mul (hxp i hi).le]; norm_num
  have hSu : ∑ i ∈ s, w i * x i ^ u = ∑ i ∈ s, w i * (x i ^ (u / 2)) ^ 2 :=
    sum_congr rfl fun i hi => by rw [hsq u i hi]
  have hSv : ∑ i ∈ s, w i * x i ^ v = ∑ i ∈ s, w i * (x i ^ (v / 2)) ^ 2 :=
    sum_congr rfl fun i hi => by rw [hsq v i hi]
  have hSα : ∑ i ∈ s, w i * x i ^ α = ∑ i ∈ s, w i * (x i ^ (u / 2) * x i ^ (v / 2)) :=
    sum_congr rfl fun i hi => by rw [← rpow_add (hxp i hi), hα]
  have hA : 0 < ∑ i ∈ s, w i * (x i ^ (u / 2)) ^ 2 :=
    sum_pos (fun i hi => by have := hw i hi; have := hxp i hi; positivity) ⟨i₀, hi₀⟩
  have hB : 0 < ∑ i ∈ s, w i * (x i ^ (v / 2)) ^ 2 :=
    sum_pos (fun i hi => by have := hw i hi; have := hxp i hi; positivity) ⟨i₀, hi₀⟩
  have hC : 0 < ∑ i ∈ s, w i * (x i ^ (u / 2) * x i ^ (v / 2)) :=
    sum_pos (fun i hi => by have := hw i hi; have := hxp i hi; positivity) ⟨i₀, hi₀⟩
  -- ratio bounds `m₁ / M₂ ≤ a / b ≤ M₁ / m₂`
  have hr : ∀ i ∈ s, m₁ / M₂ * x i ^ (v / 2) ≤ x i ^ (u / 2) := fun i hi => by
    calc m₁ / M₂ * x i ^ (v / 2) ≤ m₁ / M₂ * M₂ := by gcongr; exact (hb i hi).2
      _ = m₁ := by field_simp
      _ ≤ _ := (ha i hi).1
  have hR : ∀ i ∈ s, x i ^ (u / 2) ≤ M₁ / m₂ * x i ^ (v / 2) := fun i hi => by
    calc x i ^ (u / 2) ≤ M₁ := (ha i hi).2
      _ = M₁ / m₂ * m₂ := by field_simp
      _ ≤ _ := by gcongr; exact (hb i hi).1
  -- ratio bounds `m₂ / M₁ ≤ b / a ≤ M₂ / m₁`
  have hr' : ∀ i ∈ s, m₂ / M₁ * x i ^ (u / 2) ≤ x i ^ (v / 2) := fun i hi => by
    calc m₂ / M₁ * x i ^ (u / 2) ≤ m₂ / M₁ * M₁ := by gcongr; exact (ha i hi).2
      _ = m₂ := by field_simp
      _ ≤ _ := (hb i hi).1
  have hR' : ∀ i ∈ s, x i ^ (v / 2) ≤ M₂ / m₁ * x i ^ (u / 2) := fun i hi => by
    calc x i ^ (v / 2) ≤ M₂ := (hb i hi).2
      _ = M₂ / m₁ * m₁ := by field_simp
      _ ≤ _ := by gcongr; exact (ha i hi).1
  have hoz := ozeki_rpow s hw' hlo hx (σ := u / 2) (τ := v / 2)
  rw [← hm₁, ← hM₁, ← hm₂, ← hM₂] at hoz
  rw [hSu, hSv, hSα]
  refine ⟨⟨?_, ?_⟩, shisha_mond s hw' (by positivity) (by positivity) hr hR hC hB,
    hoz, ?_⟩
  · rw [one_le_div (by positivity)]
    exact sq_sum_le_mul s _ _ hw'
  · have hK : (√(M₁ * M₂ / (m₁ * m₂)) + √(m₁ * m₂ / (M₁ * M₂))) ^ 2 / 4 =
        (m₁ / M₂ + M₁ / m₂) ^ 2 / (4 * (m₁ / M₂) * (M₁ / m₂)) := by
      have h1 : √(M₁ * M₂ / (m₁ * m₂)) * √(m₁ * m₂ / (M₁ * M₂)) = 1 := by
        rw [← sqrt_mul (by positivity),
          show M₁ * M₂ / (m₁ * m₂) * (m₁ * m₂ / (M₁ * M₂)) = 1 by field_simp, sqrt_one]
      rw [add_sq, sq_sqrt (by positivity), sq_sqrt (by positivity), mul_assoc, h1]
      field_simp
      ring
    rw [div_le_iff₀ (by positivity), hK]
    exact polya_szego s hw' (by positivity) (by positivity) hr hR
  · have := diaz_metcalf s hw' hr' hR'
    rw [show m₂ * M₂ / (M₁ * m₁) = m₂ / M₁ * (M₂ / m₁) by field_simp, add_comm (M₂ / m₁)]
    simpa only [mul_comm (x _ ^ (v / 2))] using this

end Real
