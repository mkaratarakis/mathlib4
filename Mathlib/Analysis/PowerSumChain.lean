/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Jensen

/-!
# Chains of weighted power-sum inequalities

For weights `w i` and positive reals `x i`, `i ∈ s`, write `S γ = ∑ i ∈ s, w i * x i ^ γ` for the
weighted power sum and `W = ∑ i ∈ s, w i` for the total weight.  Dujella, Jakšetić and Pečarić
chained Hölder's inequality, Jensen's inequality and the monotonicity of power means into
inequalities of the form
`S u ^ (1 / p) * S v ^ (1 / q) ≥ S α ≥ W ^ (1 - α / β) * S β ^ (α / β) ≥ S β ≥ S α ^ (β / α)`,
where `α = u / p + v / q`, in the unweighted case `w = 1`.  This file proves the weighted chains.
Hölder's inequality and Jensen's inequality hold for arbitrary nonnegative weights; the steps
that compare `S α ^ (β / α)` with `S β` (monotonicity of `ℓ^γ` norms) need `1 ≤ w i`, and the
steps that compare `S β` with `W` need `1 ≤ x i`.

## Main results

* `Real.Lp_mul_Lq_le_inner_of_lt_one`: the reverse Hölder inequality for `0 < p < 1`.
* `Real.sum_mul_rpow_le_of_one_lt`, `Real.le_sum_mul_rpow_of_lt_one`: weighted Hölder and
  reverse Hölder for power sums.
* `Real.powerSum_chain_of_one_lt_of_le`, `Real.powerSum_chain_of_one_lt_of_lt`,
  `Real.powerSum_chain_of_lt_one_of_le`, `Real.powerSum_chain_of_lt_one_of_lt`: the four weighted
  chains (Theorems 6 and 7 of Dujella–Jakšetić–Pečarić in the case `w = 1`).

Throughout, `q` is the conjugate exponent: `p⁻¹ + q⁻¹ = 1`, so `q > 1` when `p > 1` and `q < 0`
when `0 < p < 1`.
-/

@[expose] public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {w x : ι → ℝ}

/-! ### Hölder and reverse Hölder -/

private lemma ne_zero_of_inv_add_inv_eq_one {p q : ℝ} (hpq : p⁻¹ + q⁻¹ = 1) (hp : p ≠ 1) :
    q ≠ 0 := by
  rintro rfl
  rw [inv_zero, add_zero, inv_eq_one] at hpq
  exact hp hpq

private lemma rpow_rpow_div {x a b : ℝ} (hx : 0 ≤ x) (hb : b ≠ 0) :
    (x ^ b) ^ (a / b) = x ^ a := by
  rw [← rpow_mul hx]
  congr 1
  field_simp

private lemma rpow_mul_rpow_eq {p q u v α a y : ℝ} (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (ha : 0 ≤ a) (hy : 0 < y) :
    (a * y ^ u) ^ (1 / p) * (a * y ^ v) ^ (1 / q) = a * y ^ α := by
  rw [mul_rpow ha (rpow_nonneg hy.le _), mul_rpow ha (rpow_nonneg hy.le _), ← rpow_mul hy.le,
    ← rpow_mul hy.le, mul_mul_mul_comm, ← rpow_add' ha (by rw [one_div, one_div, hpq]; simp),
    ← rpow_add hy, one_div, one_div, hpq, rpow_one, ← hα, div_eq_mul_inv, div_eq_mul_inv]

private lemma sum_rpow_le_rpow_sum {γ : ℝ} (hγ : 1 ≤ γ) {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, y i ^ γ ≤ (∑ i ∈ s, y i) ^ γ := by
  induction s using Finset.cons_induction with
  | empty => simp [zero_rpow (by linarith : γ ≠ 0)]
  | cons a s ha ih =>
    rw [sum_cons, sum_cons]
    have hy' : ∀ i ∈ s, 0 ≤ y i := fun i hi => hy i (mem_cons_of_mem hi)
    calc y a ^ γ + ∑ i ∈ s, y i ^ γ ≤ y a ^ γ + (∑ i ∈ s, y i) ^ γ := by
          gcongr; exact ih hy'
      _ ≤ _ := add_rpow_le_rpow_add (hy a (mem_cons_self a s)) (sum_nonneg hy') hγ

private lemma rpow_sum_le_sum_rpow {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : s.Nonempty)
    {y : ι → ℝ} (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, y i) ^ γ ≤ ∑ i ∈ s, y i ^ γ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [sum_cons, sum_cons]
    have hy' : ∀ i ∈ s, 0 ≤ y i := fun i hi => hy i (mem_cons_of_mem hi)
    calc (y a + ∑ i ∈ s, y i) ^ γ ≤ y a ^ γ + (∑ i ∈ s, y i) ^ γ :=
          rpow_add_le_add_rpow (hy a (mem_cons_self a s)) (sum_nonneg hy') hγ0 hγ1
      _ ≤ _ := by gcongr; exact ih hy'

private lemma sum_mul_rpow_le_rpow_sum_mul {γ : ℝ} (hγ : 1 ≤ γ) {y : ι → ℝ}
    (hw : ∀ i ∈ s, 1 ≤ w i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, w i * y i ^ γ ≤ (∑ i ∈ s, w i * y i) ^ γ := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => zero_le_one.trans (hw i hi)
  calc ∑ i ∈ s, w i * y i ^ γ ≤ ∑ i ∈ s, (w i * y i) ^ γ := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_rpow (hw0 i hi) (hy i hi)]
        refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg (hy i hi) _)
        simpa using rpow_le_rpow_of_exponent_le (hw i hi) hγ
    _ ≤ _ := sum_rpow_le_rpow_sum s hγ fun i hi => mul_nonneg (hw0 i hi) (hy i hi)

private lemma rpow_sum_mul_le_sum_mul_rpow {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hs : s.Nonempty) {y : ι → ℝ} (hw : ∀ i ∈ s, 1 ≤ w i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, w i * y i) ^ γ ≤ ∑ i ∈ s, w i * y i ^ γ := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => zero_le_one.trans (hw i hi)
  calc _ ≤ ∑ i ∈ s, (w i * y i) ^ γ :=
        rpow_sum_le_sum_rpow s hγ0 hγ1 hs fun i hi => mul_nonneg (hw0 i hi) (hy i hi)
    _ ≤ _ := sum_le_sum fun i hi => by
        rw [mul_rpow (hw0 i hi) (hy i hi)]
        refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg (hy i hi) _)
        simpa using rpow_le_rpow_of_exponent_le (hw i hi) hγ1

/-- **Reverse Hölder inequality**: for `0 < p < 1` and `p⁻¹ + q⁻¹ = 1` (so `q < 0`), and positive
`f`, `g`, `(∑ f ^ p) ^ (1 / p) * (∑ g ^ q) ^ (1 / q) ≤ ∑ f * g`. -/
theorem Lp_mul_Lq_le_inner_of_lt_one {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) ≤ ∑ i ∈ s, f i * g i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [hp0.ne']
  have hq0 : q ≠ 0 := ne_zero_of_inv_add_inv_eq_one hpq hp1.ne
  have hp1' : 1 - p ≠ 0 := sub_ne_zero.2 hp1.ne'
  have hq : 1 / q = 1 - 1 / p := by rw [one_div, one_div]; linarith
  have hqp : -p * (1 / (1 - p)) = q := by
    have : p - 1 ≠ 0 := sub_ne_zero.2 hp1.ne
    rw [← inv_inv q, ← one_div q, hq]
    field_simp
    ring
  have hPQ : (1 / p).HolderConjugate (1 / (1 - p)) := by
    refine holderConjugate_iff.2 ⟨one_lt_one_div hp0 hp1, ?_⟩
    simp
  have H := inner_le_Lp_mul_Lq_of_nonneg s hPQ (f := fun i => (f i * g i) ^ p)
    (g := fun i => g i ^ (-p)) (fun i hi => (rpow_pos_of_pos (mul_pos (hf i hi) (hg i hi)) _).le)
    (fun i hi => (rpow_pos_of_pos (hg i hi) _).le)
  have e1 : ∑ i ∈ s, (f i * g i) ^ p * g i ^ (-p) = ∑ i ∈ s, f i ^ p :=
    sum_congr rfl fun i hi => by
      rw [mul_rpow (hf i hi).le (hg i hi).le, mul_assoc, ← rpow_add (hg i hi), add_neg_cancel,
        rpow_zero, mul_one]
  have e2 : ∑ i ∈ s, ((f i * g i) ^ p) ^ (1 / p) = ∑ i ∈ s, f i * g i :=
    sum_congr rfl fun i hi => by
      rw [one_div, rpow_rpow_inv (mul_pos (hf i hi) (hg i hi)).le hp0.ne']
  have e3 : ∑ i ∈ s, (g i ^ (-p)) ^ (1 / (1 - p)) = ∑ i ∈ s, g i ^ q :=
    sum_congr rfl fun i hi => by rw [← rpow_mul (hg i hi).le, hqp]
  simp only [one_div_one_div] at H
  rw [e1, e2, e3] at H
  have hA : 0 < ∑ i ∈ s, f i * g i := sum_pos (fun i hi => mul_pos (hf i hi) (hg i hi)) hs
  have hB : 0 < ∑ i ∈ s, g i ^ q := sum_pos (fun i hi => rpow_pos_of_pos (hg i hi) _) hs
  calc (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)
      ≤ ((∑ i ∈ s, f i * g i) ^ p * (∑ i ∈ s, g i ^ q) ^ (1 - p)) ^ (1 / p) *
          (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
        refine mul_le_mul_of_nonneg_right (rpow_le_rpow ?_ H (by positivity)) (by positivity)
        exact sum_nonneg fun i hi => (rpow_pos_of_pos (hf i hi) _).le
    _ = (∑ i ∈ s, f i * g i) * ((∑ i ∈ s, g i ^ q) ^ ((1 - p) * (1 / p)) *
          (∑ i ∈ s, g i ^ q) ^ (1 / q)) := by
        rw [mul_rpow (by positivity) (by positivity), ← rpow_mul hA.le, ← rpow_mul hB.le,
          mul_one_div_cancel hp0.ne', rpow_one, mul_assoc]
    _ = ∑ i ∈ s, f i * g i := by
        rw [← rpow_add hB, hq, show (1 - p) * (1 / p) + (1 - 1 / p) = 0 by field_simp; ring,
          rpow_zero, mul_one]

/-- **Weighted Hölder inequality for power sums**: for `p > 1`, `p⁻¹ + q⁻¹ = 1` and
`α = u / p + v / q`, `S α ≤ S u ^ (1 / p) * S v ^ (1 / q)`. -/
theorem sum_mul_rpow_le_of_one_lt {p q u v α : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) := by
  have hpq' : p.HolderConjugate q := holderConjugate_iff.2 ⟨hp, hpq⟩
  have hp0 : p ≠ 0 := by positivity
  have hq0 : q ≠ 0 := ne_zero_of_inv_add_inv_eq_one hpq hp.ne'
  have H := inner_le_Lp_mul_Lq_of_nonneg s hpq' (f := fun i => (w i * x i ^ u) ^ (1 / p))
    (g := fun i => (w i * x i ^ v) ^ (1 / q))
    (fun i hi => rpow_nonneg (mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)) _)
    (fun i hi => rpow_nonneg (mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)) _)
  have e1 : ∑ i ∈ s, (w i * x i ^ u) ^ (1 / p) * (w i * x i ^ v) ^ (1 / q) =
      ∑ i ∈ s, w i * x i ^ α :=
    sum_congr rfl fun i hi => rpow_mul_rpow_eq hpq hα (hw i hi) (hx i hi)
  have e2 : ∑ i ∈ s, ((w i * x i ^ u) ^ (1 / p)) ^ p = ∑ i ∈ s, w i * x i ^ u :=
    sum_congr rfl fun i hi => by
      rw [one_div, rpow_inv_rpow (mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)) hp0]
  have e3 : ∑ i ∈ s, ((w i * x i ^ v) ^ (1 / q)) ^ q = ∑ i ∈ s, w i * x i ^ v :=
    sum_congr rfl fun i hi => by
      rw [one_div, rpow_inv_rpow (mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)) hq0]
  rwa [e1, e2, e3] at H

/-- **Weighted reverse Hölder inequality for power sums**: for `0 < p < 1`, `p⁻¹ + q⁻¹ = 1` and
`α = u / p + v / q`, `S u ^ (1 / p) * S v ^ (1 / q) ≤ S α`. -/
theorem le_sum_mul_rpow_of_lt_one {p q u v α : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hw : ∀ i ∈ s, 0 < w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  have hp1' : p ≠ 1 := hp1.ne
  have hq0 : q ≠ 0 := ne_zero_of_inv_add_inv_eq_one hpq hp1'
  have H := Lp_mul_Lq_le_inner_of_lt_one s hp0 hp1 hpq
    (f := fun i => (w i * x i ^ u) ^ (1 / p)) (g := fun i => (w i * x i ^ v) ^ (1 / q))
    (fun i hi => rpow_pos_of_pos (mul_pos (hw i hi) (rpow_pos_of_pos (hx i hi) _)) _)
    (fun i hi => rpow_pos_of_pos (mul_pos (hw i hi) (rpow_pos_of_pos (hx i hi) _)) _)
  have e1 : ∑ i ∈ s, (w i * x i ^ u) ^ (1 / p) * (w i * x i ^ v) ^ (1 / q) =
      ∑ i ∈ s, w i * x i ^ α :=
    sum_congr rfl fun i hi => rpow_mul_rpow_eq hpq hα (hw i hi).le (hx i hi)
  have e2 : ∑ i ∈ s, ((w i * x i ^ u) ^ (1 / p)) ^ p = ∑ i ∈ s, w i * x i ^ u :=
    sum_congr rfl fun i hi => by
      rw [one_div, rpow_inv_rpow (mul_pos (hw i hi) (rpow_pos_of_pos (hx i hi) _)).le hp0.ne']
  have e3 : ∑ i ∈ s, ((w i * x i ^ v) ^ (1 / q)) ^ q = ∑ i ∈ s, w i * x i ^ v :=
    sum_congr rfl fun i hi => by
      rw [one_div, rpow_inv_rpow (mul_pos (hw i hi) (rpow_pos_of_pos (hx i hi) _)).le hq0]
  rwa [e1, e2, e3] at H

/-! ### Power means (Jensen) -/

/-- Jensen's inequality for the convex power `y ↦ y ^ (α / β)`, `0 < β ≤ α`:
`W ^ (1 - α / β) * S β ^ (α / β) ≤ S α`. -/
theorem rpow_mean_le_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ α := by
  have hγ : 1 ≤ α / β := (one_le_div hβ).2 hβα
  have hS : 0 ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  have key := rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / ∑ j ∈ s, w j)
    (fun i => x i ^ β) (fun i hi => div_nonneg (hw i hi) hW.le)
    (by rw [← sum_div, div_self hW.ne']) (fun i hi => rpow_nonneg (hx i hi).le _) hγ
  have e1 : ∑ i ∈ s, w i / (∑ j ∈ s, w j) * x i ^ β =
      (∑ i ∈ s, w i * x i ^ β) / ∑ j ∈ s, w j := by
    rw [sum_div]; exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ s, w i / (∑ j ∈ s, w j) * (x i ^ β) ^ (α / β) =
      (∑ i ∈ s, w i * x i ^ α) / ∑ j ∈ s, w j := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    rw [rpow_rpow_div (hx i hi).le hβ.ne']
    ring
  rw [e1, e2, div_rpow hS hW.le] at key
  rw [rpow_sub hW, rpow_one]
  calc (∑ i ∈ s, w i) / (∑ i ∈ s, w i) ^ (α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β)
      = (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * x i ^ β) ^ (α / β) / (∑ i ∈ s, w i) ^ (α / β)) := by
        ring
    _ ≤ (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * x i ^ α) / ∑ i ∈ s, w i) := by gcongr
    _ = ∑ i ∈ s, w i * x i ^ α := by field_simp

/-- Jensen's inequality for the concave power `y ↦ y ^ (α / β)`, `0 < α ≤ β`:
`S α ≤ W ^ (1 - α / β) * S β ^ (α / β)`. -/
theorem le_rpow_mean_of_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  have hγ0 : 0 ≤ α / β := div_nonneg hα.le (hα.trans_le hαβ).le
  have hγ1 : α / β ≤ 1 := (div_le_one (hα.trans_le hαβ)).2 hαβ
  have hS : 0 ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (rpow_nonneg (hx i hi).le _)
  have key := (concaveOn_rpow hγ0 hγ1).le_map_sum (t := s) (w := fun i => w i / ∑ j ∈ s, w j)
    (p := fun i => x i ^ β) (fun i hi => div_nonneg (hw i hi) hW.le)
    (by rw [← sum_div, div_self hW.ne']) (fun i hi => Set.mem_Ici.2 (rpow_nonneg (hx i hi).le _))
  have e1 : ∑ i ∈ s, w i / (∑ j ∈ s, w j) * x i ^ β =
      (∑ i ∈ s, w i * x i ^ β) / ∑ j ∈ s, w j := by
    rw [sum_div]; exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ s, w i / (∑ j ∈ s, w j) * (x i ^ β) ^ (α / β) =
      (∑ i ∈ s, w i * x i ^ α) / ∑ j ∈ s, w j := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    rw [rpow_rpow_div (hx i hi).le (hα.trans_le hαβ).ne']
    ring
  simp only [smul_eq_mul] at key
  rw [e1, e2, div_rpow hS hW.le] at key
  rw [rpow_sub hW, rpow_one]
  calc ∑ i ∈ s, w i * x i ^ α = (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * x i ^ α) / ∑ i ∈ s, w i) := by
        field_simp
    _ ≤ (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * x i ^ β) ^ (α / β) / (∑ i ∈ s, w i) ^ (α / β)) := by
        gcongr
    _ = _ := by ring

/-! ### Comparisons using `1 ≤ x i` -/

/-- If `1 ≤ x i` and `0 < β ≤ α`, then `S β ≤ W ^ (1 - α / β) * S β ^ (α / β)`. -/
theorem sum_le_mean_rpow_of_one_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ β ≤
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  have hWS : ∑ i ∈ s, w i ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_le_sum fun i hi => le_mul_of_one_le_right (hw i hi) (one_le_rpow (hx i hi) hβ.le)
  have hS : 0 < ∑ i ∈ s, w i * x i ^ β := hW.trans_le hWS
  have hc : 0 ≤ α / β - 1 := by rw [sub_nonneg]; exact (one_le_div hβ).2 hβα
  have hWc : 0 < (∑ i ∈ s, w i) ^ (α / β - 1) := rpow_pos_of_pos hW _
  rw [show 1 - α / β = -(α / β - 1) by ring, rpow_neg hW.le, ← div_eq_inv_mul,
    le_div_iff₀ hWc]
  calc (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i) ^ (α / β - 1)
      ≤ (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β - 1) := by
        gcongr
    _ = _ := by rw [rpow_sub_one hS.ne']; field_simp

/-- If `1 ≤ x i` and `0 < α ≤ β`, then `W ^ (1 - α / β) * S β ^ (α / β) ≤ S β`. -/
theorem mean_rpow_le_sum_of_one_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
      ∑ i ∈ s, w i * x i ^ β := by
  have hWS : ∑ i ∈ s, w i ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_le_sum fun i hi => le_mul_of_one_le_right (hw i hi) (one_le_rpow (hx i hi)
      (hα.trans_le hαβ).le)
  have hS : 0 < ∑ i ∈ s, w i * x i ^ β := hW.trans_le hWS
  have hc : α / β - 1 ≤ 0 := by
    rw [sub_nonpos]; exact (div_le_one (hα.trans_le hαβ)).2 hαβ
  have hWc : 0 < (∑ i ∈ s, w i) ^ (α / β - 1) := rpow_pos_of_pos hW _
  rw [show 1 - α / β = -(α / β - 1) by ring, rpow_neg hW.le, ← div_eq_inv_mul,
    div_le_iff₀ hWc]
  calc (∑ i ∈ s, w i * x i ^ β) ^ (α / β)
      = (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β - 1) := by
        rw [rpow_sub_one hS.ne']; field_simp
    _ ≤ (∑ i ∈ s, w i * x i ^ β) * (∑ i ∈ s, w i) ^ (α / β - 1) := by
        exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hW hWS hc) hS.le

/-! ### Monotonicity of weighted `ℓ^γ` norms, using `1 ≤ w i` -/

/-- If `1 ≤ w i` and `0 < β ≤ α`, then `S α ≤ S β ^ (α / β)`. -/
theorem sum_rpow_le_rpow_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 1 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤ (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  have hγ : 1 ≤ α / β := (one_le_div hβ).2 hβα
  calc ∑ i ∈ s, w i * x i ^ α = ∑ i ∈ s, w i * (x i ^ β) ^ (α / β) :=
        sum_congr rfl fun i hi => by rw [rpow_rpow_div (hx i hi).le hβ.ne']
    _ ≤ _ := sum_mul_rpow_le_rpow_sum_mul s hγ hw fun i hi => rpow_nonneg (hx i hi).le _

/-- If `1 ≤ w i` and `0 < β ≤ α`, then `S α ^ (β / α) ≤ S β`. -/
theorem sum_rpow_rpow_le_of_le {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (hw : ∀ i ∈ s, 1 ≤ w i)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ α) ^ (β / α) ≤ ∑ i ∈ s, w i * x i ^ β := by
  have hα : 0 < α := hβ.trans_le hβα
  have hS : 0 ≤ ∑ i ∈ s, w i * x i ^ β :=
    sum_nonneg fun i hi => mul_nonneg (zero_le_one.trans (hw i hi)) (rpow_nonneg (hx i hi).le _)
  calc (∑ i ∈ s, w i * x i ^ α) ^ (β / α)
      ≤ ((∑ i ∈ s, w i * x i ^ β) ^ (α / β)) ^ (β / α) :=
        rpow_le_rpow (sum_nonneg fun i hi => mul_nonneg (zero_le_one.trans (hw i hi))
          (rpow_nonneg (hx i hi).le _)) (sum_rpow_le_rpow_of_le s hβ hβα hw hx) (by positivity)
    _ = ∑ i ∈ s, w i * x i ^ β := by
        rw [← rpow_mul hS, show α / β * (β / α) = 1 by field_simp, rpow_one]

/-- If `1 ≤ w i`, `s` is nonempty and `0 ≤ α ≤ β` with `0 < β`, then `S β ^ (α / β) ≤ S α`. -/
theorem rpow_le_sum_rpow_of_le {α β : ℝ} (hs : s.Nonempty) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : 0 < β) (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤ ∑ i ∈ s, w i * x i ^ α := by
  have hγ0 : 0 ≤ α / β := by positivity
  have hγ1 : α / β ≤ 1 := (div_le_one hβ).2 hαβ
  calc _ ≤ ∑ i ∈ s, w i * (x i ^ β) ^ (α / β) :=
        rpow_sum_mul_le_sum_mul_rpow s hγ0 hγ1 hs hw fun i hi => rpow_nonneg (hx i hi).le _
    _ = _ := sum_congr rfl fun i hi => by rw [rpow_rpow_div (hx i hi).le hβ.ne']

/-! ### The four chains -/

/-- **Weighted power-sum chain, `p > 1`, `α ≥ β`** (Dujella–Jakšetić–Pečarić, Theorem 6(i),
for `w = 1`). -/
theorem powerSum_chain_of_one_lt_of_le {p q u v α β : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hβ : 0 < β) (hβα : β ≤ α) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
        (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ∧
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
        ∑ i ∈ s, w i * x i ^ α ∧
      ∑ i ∈ s, w i * x i ^ β ≤
        (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ∧
      (∑ i ∈ s, w i * x i ^ α) ^ (β / α) ≤ ∑ i ∈ s, w i * x i ^ β := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => zero_le_one.trans (hw i hi)
  have hx0 : ∀ i ∈ s, 0 < x i := fun i hi => zero_lt_one.trans_le (hx i hi)
  have hW : 0 < ∑ i ∈ s, w i := sum_pos (fun i hi => zero_lt_one.trans_le (hw i hi)) hs
  exact ⟨sum_mul_rpow_le_of_one_lt s hp hpq hα hw0 hx0, rpow_mean_le_of_le s hβ hβα hw0 hW hx0,
    sum_le_mean_rpow_of_one_le s hβ hβα hw0 hW hx, sum_rpow_rpow_le_of_le s hβ hβα hw hx0⟩

/-- **Weighted power-sum chain, `p > 1`, `0 ≤ α < β`** (Dujella–Jakšetić–Pečarić,
Theorem 6(ii), for `w = 1`). -/
theorem powerSum_chain_of_one_lt_of_lt {p q u v α β : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1)
    (hα : u / p + v / q = α) (hα0 : 0 ≤ α) (hαβ : α < β) (hs : s.Nonempty)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * x i ^ α ≤
        (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ∧
      (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤ ∑ i ∈ s, w i * x i ^ α := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => zero_le_one.trans (hw i hi)
  exact ⟨sum_mul_rpow_le_of_one_lt s hp hpq hα hw0 hx,
    rpow_le_sum_rpow_of_le s hs hα0 hαβ.le (hα0.trans_lt hαβ) hw hx⟩

/-- **Weighted power-sum chain, `0 < p < 1`, `α ≥ β`** (Dujella–Jakšetić–Pečarić,
Theorem 7(i), for `w = 1`). -/
theorem powerSum_chain_of_lt_one_of_le {p q u v α β : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hβ : 0 < β) (hβα : β ≤ α)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
        ∑ i ∈ s, w i * x i ^ α ∧
      ∑ i ∈ s, w i * x i ^ α ≤ (∑ i ∈ s, w i * x i ^ β) ^ (α / β) := by
  have hw0 : ∀ i ∈ s, 0 < w i := fun i hi => zero_lt_one.trans_le (hw i hi)
  exact ⟨le_sum_mul_rpow_of_lt_one s hp0 hp1 hpq hα hw0 hx, sum_rpow_le_rpow_of_le s hβ hβα hw hx⟩

/-- **Weighted power-sum chain, `0 < p < 1`, `0 < α < β`** (Dujella–Jakšetić–Pečarić,
Theorem 7(ii), for `w = 1`). -/
theorem powerSum_chain_of_lt_one_of_lt {p q u v α β : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p⁻¹ + q⁻¹ = 1) (hα : u / p + v / q = α) (hα0 : 0 < α) (hαβ : α < β)
    (hs : s.Nonempty) (hw : ∀ i ∈ s, 1 ≤ w i) (hx : ∀ i ∈ s, 1 ≤ x i) :
    (∑ i ∈ s, w i * x i ^ u) ^ (1 / p) * (∑ i ∈ s, w i * x i ^ v) ^ (1 / q) ≤
        ∑ i ∈ s, w i * x i ^ α ∧
      ∑ i ∈ s, w i * x i ^ α ≤
        (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ∧
      (∑ i ∈ s, w i) ^ (1 - α / β) * (∑ i ∈ s, w i * x i ^ β) ^ (α / β) ≤
        ∑ i ∈ s, w i * x i ^ β ∧
      ∑ i ∈ s, w i * x i ^ β ≤ (∑ i ∈ s, w i * x i ^ α) ^ (β / α) := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => zero_le_one.trans (hw i hi)
  have hx0 : ∀ i ∈ s, 0 < x i := fun i hi => zero_lt_one.trans_le (hx i hi)
  have hW : 0 < ∑ i ∈ s, w i := sum_pos (fun i hi => zero_lt_one.trans_le (hw i hi)) hs
  exact ⟨le_sum_mul_rpow_of_lt_one s hp0 hp1 hpq hα (fun i hi => zero_lt_one.trans_le (hw i hi))
    hx0, le_rpow_mean_of_le s hα0 hαβ.le hw0 hW hx0,
    mean_rpow_le_sum_of_one_le s hα0 hαβ.le hw0 hW hx, sum_rpow_le_rpow_of_le s hα0 hαβ.le hw hx0⟩

end Real
