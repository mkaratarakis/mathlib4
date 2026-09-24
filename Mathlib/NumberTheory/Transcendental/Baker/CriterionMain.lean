/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.Transcendental.Baker.Criterion

/-!
# The criterion of Schneider–Lang: parameters and conclusion

The choice of parameters for the transcendence argument of
`Mathlib/NumberTheory/Transcendental/Baker/Criterion.lean` (step 6 of §4.6 of Waldschmidt,
*Diophantine Approximation on Linear Algebraic Groups*), and the resulting proof of
Corollary 4.2.

## Main statements

* `Transcendental.SchneiderLangProof.exists_parameters`: admissible parameters exist.
* `Transcendental.SchneiderLangProof.main`: Corollary 4.2.
-/

@[expose] public section

open Finset MultiIndex NumberField

namespace Transcendental.SchneiderLangProof

variable {n d₀ d₁ : ℕ}

/-- The exponent of the Liouville factor. -/
noncomputable def phiE (d₀ d₁ n T S₁ δ D : ℕ) (N Hg : ℝ) (M : ℕ) : ℝ :=
  M * Real.log M + D * (Real.log (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) +
    ((d₀ * T + M + d₁ * n * T * S₁ : ℕ) : ℝ) * Real.log δ + N +
    ((d₀ * T : ℕ) : ℝ) * Real.log ((δ : ℝ) ^ 2 * M + n * S₁ * Hg + 1) +
    M * Real.log (d₁ * T * Hg + 1) + ((d₁ * n * T * S₁ : ℕ) : ℝ) * Real.log Hg)

lemma natPow_eq_exp (M : ℕ) : (M : ℝ) ^ M = Real.exp (M * Real.log M) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · rw [← Real.log_pow, Real.exp_log (by positivity)]

lemma liouvilleFactor_le_exp {d₀ d₁ n T S₁ δ D : ℕ} (hD : 1 ≤ D) (hδ : 1 ≤ δ) {N Hg : ℝ}
    (hN : 0 ≤ N) (hHg : 1 ≤ Hg) (M : ℕ) :
    liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M ≤ Real.exp (phiE d₀ d₁ n T S₁ δ D N Hg M) := by
  unfold liouvilleFactor phiE
  set c : ℝ := (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) with hc
  set A : ℕ := d₀ * T + M + d₁ * n * T * S₁ with hA
  set Q : ℝ := (δ : ℝ) ^ 2 * M + n * S₁ * Hg + 1 with hQ
  set W : ℝ := d₁ * T * Hg + 1 with hW
  set Y : ℝ := (δ : ℝ) ^ A * Real.exp N * Q ^ (d₀ * T) * W ^ M * Hg ^ (d₁ * n * T * S₁)
    with hY
  have hδ1 : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hc1 : 1 ≤ c := by
    rw [hc]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ (δ : ℝ) ^ 2 * M + n * S₁ * Hg := by positivity
    linarith
  have hW1 : 1 ≤ W := by
    have : (0 : ℝ) ≤ d₁ * T * Hg := by positivity
    linarith
  have hδA : 1 ≤ (δ : ℝ) ^ A := one_le_pow₀ hδ1
  have hY1 : (δ : ℝ) ^ A ≤ Y := by
    rw [hY]
    have h1 : 1 ≤ Real.exp N := Real.one_le_exp hN
    have h2 : 1 ≤ Q ^ (d₀ * T) := one_le_pow₀ hQ1
    have h3 : 1 ≤ W ^ M := one_le_pow₀ hW1
    have h4 : 1 ≤ Hg ^ (d₁ * n * T * S₁) := one_le_pow₀ hHg
    calc (δ : ℝ) ^ A = (δ : ℝ) ^ A * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hX : (δ : ℝ) ^ A ≤ c * Y := hY1.trans (le_mul_of_one_le_left (by linarith) hc1)
  have hX0 : 0 < c * Y := lt_of_lt_of_le (by positivity) hX
  have hlogX : Real.log (c * Y) = Real.log c + (A : ℝ) * Real.log δ + N +
      ((d₀ * T : ℕ) : ℝ) * Real.log Q + M * Real.log W +
        ((d₁ * n * T * S₁ : ℕ) : ℝ) * Real.log Hg := by
    have hδ0 : (δ : ℝ) ≠ 0 := by positivity
    rw [hY, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  calc (M : ℝ) ^ M * (δ : ℝ) ^ A * (c * Y) ^ (D - 1)
      ≤ (M : ℝ) ^ M * (c * Y) * (c * Y) ^ (D - 1) := by gcongr
    _ = (M : ℝ) ^ M * (c * Y) ^ D := by
        rw [mul_assoc, ← pow_succ']
        congr 2
        omega
    _ = Real.exp (M * Real.log M) * Real.exp (D * Real.log (c * Y)) := by
        have h2 : (c * Y) ^ D = Real.exp (D * Real.log (c * Y)) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos hX0 D)]
        rw [natPow_eq_exp, h2]
    _ = _ := by
        rw [← Real.exp_add, hlogX]

lemma growth_eq {d₀ d₁ T : ℕ} {N Ax ρ : ℝ} (hρ : 0 ≤ ρ) :
    growth d₀ d₁ T N Ax ρ = Real.exp (Real.log (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) + N +
      ((d₀ * T : ℕ) : ℝ) * Real.log (1 + ρ) + T * Ax * ρ) := by
  unfold growth
  have hc : (0 : ℝ) < (((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) : ℝ) := by positivity
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hc, ← Real.log_pow,
    Real.exp_log (by positivity)]
  push_cast
  ring

/-!
### Elementary estimates
-/

lemma log_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · linarith [Real.log_le_sub_one_of_pos hx]

lemma log_add_one_le {x : ℝ} (hx : 0 ≤ x) : Real.log (x + 1) ≤ x := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x + 1)]

/-- `x ^ α log x ≤ x / (1 - α)` for `x ≥ 0` and `α < 1`. -/
lemma rpow_mul_log_le {x α : ℝ} (hx : 1 ≤ x) (hα : α < 1) :
    x ^ α * Real.log x ≤ x / (1 - α) := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (by linarith : 0 < 1 - α)
  have hx0 : 0 < x := by linarith
  calc x ^ α * Real.log x ≤ x ^ α * (x ^ (1 - α) / (1 - α)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = x / (1 - α) := by
        rw [mul_div_assoc', ← Real.rpow_add hx0]
        simp

/-- `q ^ n ≤ (q ^ d) ^ (n / d)`, as an equality, for `d ≠ 0`. -/
lemma pow_eq_rpow_div {q : ℝ} (hq : 0 ≤ q) {n d : ℕ} (hd : d ≠ 0) :
    q ^ n = (q ^ d) ^ ((n : ℝ) / d) := by
  rw [← Real.rpow_natCast q d, ← Real.rpow_mul hq, mul_div_cancel₀ _ (by exact_mod_cast hd),
    Real.rpow_natCast]

/-- The linear bookkeeping at the end of `hbig_of_large`, over plain real variables. -/
lemma exponent_lt_zero {Mr lM D d n S₁ K₁ c₃ α lK lδ CQ CW Cr Cρ lH Ax d₀ d₁ C₇ lc cA Nq cd lQ
      lW cH ln ck lρ TAρ : ℝ} (hMpos : 0 < Mr)
    (e1 : D * lc ≤ D * (d * (2 * K₁ * Mr)))
    (e2 : D * (cA * lδ) ≤ D * (lδ * ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) * Mr))
    (hDN : D * Nq ≤ c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM))
    (e3 : D * (cd * lQ) ≤ D * (d₀ * (2 * K₁) * (CQ + d) * Mr))
    (e4 : D * (Mr * lW) ≤ D * (α * (Mr * lM) + (CW + α * lK) * Mr))
    (e5 : D * (cH * lH) ≤ D * (d₁ * n * S₁ * lH * (2 * K₁) * Mr))
    (hlogn : ln ≤ n * Mr) (hkM : S₁ / (2 * n * d) * (Mr * lM) ≤ ck * (lM / d))
    (hc : lc ≤ d * (2 * K₁ * Mr)) (hN1 : Nq ≤ c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM))
    (hρ : cd * lρ ≤ d₀ * (2 * K₁) * (Cr + d) * Mr) (hTρ : TAρ ≤ 2 * K₁ * Ax * Cρ * Mr)
    (hS₁M : (2 + D * α + c₃ * K₁ / d) * (Mr * lM) ≤ S₁ / (2 * n * d) * (Mr * lM))
    (hMl : Mr * (C₇ + 1) ≤ Mr * lM)
    (hC₇ : C₇ = D * d * (2 * K₁) + D * lδ * ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) +
      c₃ * K₁ / d * lK + D * d₀ * (2 * K₁) * (CQ + d) + D * (CW + α * lK) +
      D * d₁ * n * S₁ * lH * (2 * K₁) + n + d * (2 * K₁) + d₀ * (2 * K₁) * (Cr + d) +
      2 * K₁ * Ax * Cρ) :
    Mr * lM + D * (lc + cA * lδ + Nq + cd * lQ + Mr * lW + cH * lH) + ln + -(ck * (lM / d)) +
      (lc + Nq + cd * lρ + TAρ) < 0 := by
  subst hC₇
  have hcD : c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM) + c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM) =
      c₃ * K₁ / d * lK * Mr + c₃ * K₁ / d * (Mr * lM) := by ring
  linarith

/-- **The extrapolation inequality**: the condition `hbig` of `core` holds for all large `M`,
with `T = q ^ n`, `N = c₃ q ^ d log q / (4D)` and `E' = M ^ (1 / d)`, provided
`q ^ d ≤ 2 K₁ M`. -/
theorem hbig_of_large {n d₀ d₁ D δ K₁ S₁ : ℕ} (hn1 : 1 ≤ n) (hd : n + 1 ≤ d₀ + d₁)
    (hD : 1 ≤ D) (hδ : 1 ≤ δ) (hK₁ : 1 ≤ K₁) {Hg Ax Ay B c₃ : ℝ} (hHg : 1 ≤ Hg) (hAx : 0 ≤ Ax)
    (hAy : 0 ≤ Ay) (hB : 0 ≤ B) (hc₃ : 0 < c₃)
    (hS₁ : 2 * n * ((d₀ + d₁ : ℕ) : ℝ) *
      (2 + D * n / ((d₀ + d₁ : ℕ) : ℝ) + c₃ * K₁ / ((d₀ + d₁ : ℕ) : ℝ)) ≤ (S₁ : ℝ)) :
    ∃ Mstar : ℕ, ∀ q M : ℕ, 1 ≤ q → Mstar ≤ M → ((q : ℝ) ^ (d₀ + d₁) ≤ 2 * K₁ * M) →
      liouvilleFactor d₀ d₁ n (q ^ n) S₁ δ D (c₃ * q ^ (d₀ + d₁) * Real.log q / (4 * D)) Hg M *
        (n * (1 / Real.exp (Real.log M / ((d₀ + d₁ : ℕ) : ℝ))) ^ (M / n * S₁) *
          growth d₀ d₁ (q ^ n) (c₃ * q ^ (d₀ + d₁) * Real.log q / (4 * D)) Ax
            (Ay * (5 * 3 ^ n * Real.exp (Real.log M / ((d₀ + d₁ : ℕ) : ℝ)) *
              (S₁ + 2 * B)))) < 1 := by
  set d : ℕ := d₀ + d₁ with hddef
  have hd0 : 0 < d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hdpos : (0 : ℝ) < d := by linarith
  set α : ℝ := (n : ℝ) / d with hα
  have hα0 : 0 ≤ α := by positivity
  have hαd : α + 1 / d ≤ 1 := by
    rw [hα, ← add_div, div_le_one hdpos]
    exact_mod_cast hd
  have hα1 : α < 1 := by
    have : 0 < 1 / (d : ℝ) := by positivity
    linarith
  have h1α : 1 / (1 - α) ≤ d := by
    rw [div_le_iff₀ (by linarith)]
    have : (d : ℝ) * (1 / d) = 1 := by field_simp
    nlinarith
  have hK₁R : (1 : ℝ) ≤ K₁ := by exact_mod_cast hK₁
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set lδ := Real.log δ with hlδ
  set lH := Real.log Hg with hlH
  set lK := Real.log (2 * K₁) with hlK
  have hlδ0 : 0 ≤ lδ := Real.log_nonneg hδR
  have hlH0 : 0 ≤ lH := Real.log_nonneg hHg
  have hlK0 : 0 ≤ lK := Real.log_nonneg (by linarith)
  set CQ := Real.log ((δ : ℝ) ^ 2 + n * S₁ * Hg + 1) with hCQ
  have hCQ0 : 0 ≤ CQ := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (δ : ℝ) ^ 2 + n * S₁ * Hg := by positivity
    linarith)
  set CW := Real.log (d₁ * Hg + 1) with hCW
  have hCW0 : 0 ≤ CW := Real.log_nonneg (by
    have : (0 : ℝ) ≤ d₁ * Hg := by positivity
    linarith)
  set Cρ : ℝ := Ay * (5 * 3 ^ n) * (S₁ + 2 * B) with hCρ
  have hCρ0 : 0 ≤ Cρ := by positivity
  set Cr := Real.log (1 + Cρ) with hCr
  have hCr0 : 0 ≤ Cr := Real.log_nonneg (by linarith)
  set C₇ : ℝ := D * d * (2 * K₁) + D * lδ * ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) +
    c₃ * K₁ / d * lK + D * d₀ * (2 * K₁) * (CQ + d) + D * (CW + α * lK) +
    D * d₁ * n * S₁ * lH * (2 * K₁) + n + d * (2 * K₁) + d₀ * (2 * K₁) * (Cr + d) +
    2 * K₁ * Ax * Cρ with hC₇
  refine ⟨⌈Real.exp (C₇ + 1)⌉₊ + n + 1, fun q M hq hM hqM => ?_⟩
  set Mr : ℝ := (M : ℝ) with hMr
  have hMn : n ≤ M := by omega
  have hM1 : (1 : ℝ) ≤ Mr := by rw [hMr]; exact_mod_cast (by omega : 1 ≤ M)
  have hMpos : 0 < Mr := by linarith
  set lM := Real.log Mr with hlM
  have hlMC : C₇ + 1 ≤ lM := by
    have h1 : Real.exp (C₇ + 1) ≤ Mr := by
      rw [hMr]
      calc Real.exp (C₇ + 1) ≤ ⌈Real.exp (C₇ + 1)⌉₊ := Nat.le_ceil _
        _ ≤ M := by exact_mod_cast (by omega : ⌈Real.exp (C₇ + 1)⌉₊ ≤ M)
    exact (Real.le_log_iff_exp_le hMpos).2 h1
  have hlM0 : 0 ≤ lM := Real.log_nonneg hM1
  -- bounds for `T = q ^ n` in terms of `M`
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set Tr : ℝ := (q : ℝ) ^ n with hTr
  have hT1 : 1 ≤ Tr := one_le_pow₀ hq1
  set τ : ℝ := (2 * K₁ * Mr) ^ α with hτ
  have hTτ : Tr ≤ τ := by
    rw [hTr, pow_eq_rpow_div (by linarith) hd0.ne']
    exact Real.rpow_le_rpow (by positivity) hqM hα0
  have hτ_le : τ ≤ 2 * K₁ * Mr ^ α := by
    rw [hτ, Real.mul_rpow (by positivity) hMpos.le]
    have : (2 * (K₁ : ℝ)) ^ α ≤ 2 * K₁ := by
      calc (2 * (K₁ : ℝ)) ^ α ≤ (2 * K₁) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hα1.le
        _ = 2 * K₁ := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hMα : Mr ^ α ≤ Mr := by
    calc Mr ^ α ≤ Mr ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hα1.le
      _ = Mr := Real.rpow_one _
  have hMαlog : Mr ^ α * lM ≤ d * Mr := by
    calc Mr ^ α * lM ≤ Mr / (1 - α) := rpow_mul_log_le hM1 hα1
      _ = Mr * (1 / (1 - α)) := by ring
      _ ≤ Mr * d := mul_le_mul_of_nonneg_left h1α hMpos.le
      _ = d * Mr := by ring
  have hτ1 : 1 ≤ τ := hT1.trans hTτ
  have hT2 : Tr ≤ 2 * K₁ * Mr :=
    hTτ.trans (hτ_le.trans (mul_le_mul_of_nonneg_left hMα (by positivity)))
  have hT3 : Tr * lM ≤ 2 * K₁ * d * Mr := by
    calc Tr * lM ≤ (2 * K₁ * Mr ^ α) * lM :=
          mul_le_mul_of_nonneg_right (hTτ.trans hτ_le) hlM0
      _ = 2 * K₁ * (Mr ^ α * lM) := by ring
      _ ≤ 2 * K₁ * (d * Mr) := mul_le_mul_of_nonneg_left hMαlog (by positivity)
      _ = 2 * K₁ * d * Mr := by ring
  -- the parameter `N`
  set Nq : ℝ := c₃ * q ^ d * Real.log q / (4 * D) with hNq
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogq : Real.log q ≤ (lK + lM) / d := by
    rw [le_div_iff₀ hdpos, mul_comm, ← Real.log_pow, hlK, hlM,
      ← Real.log_mul (by positivity) hMpos.ne']
    exact Real.log_le_log (by positivity) hqM
  have hN0 : 0 ≤ Nq := by positivity
  have hDN : D * Nq ≤ c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM) := by
    have hD0 : (D : ℝ) ≠ 0 := by positivity
    calc D * Nq = c₃ * (q : ℝ) ^ d * Real.log q / 4 := by rw [hNq]; field_simp
      _ ≤ c₃ * (2 * K₁ * Mr) * ((lK + lM) / d) / 4 := by gcongr
      _ = c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM) := by field_simp; ring
  have hN1 : Nq ≤ c₃ * K₁ / (2 * d) * (Mr * lK + Mr * lM) :=
    (le_mul_of_one_le_left hN0 hDR).trans hDN
  -- the exponential factor `E' = M ^ (1 / d)`
  set Ep := Real.exp (lM / d) with hEp
  have hEp_rpow : Ep = Mr ^ (1 / (d : ℝ)) := by
    rw [hEp, Real.rpow_def_of_pos hMpos, hlM, mul_one_div]
  have hEp1 : 1 ≤ Ep := Real.one_le_exp (by positivity)
  -- the individual terms
  have hc : Real.log ((((q ^ n + 1) ^ d₀ * (q ^ n + 1) ^ d₁ : ℕ) : ℝ)) ≤ d * (2 * K₁ * Mr) := by
    have : ((((q ^ n + 1) ^ d₀ * (q ^ n + 1) ^ d₁ : ℕ) : ℝ)) = (Tr + 1) ^ d := by
      rw [hTr, hddef, pow_add]
      push_cast
      ring
    rw [this, Real.log_pow]
    calc (d : ℝ) * Real.log (Tr + 1) ≤ d * Tr :=
          mul_le_mul_of_nonneg_left (log_add_one_le (by linarith)) (by positivity)
      _ ≤ d * (2 * K₁ * Mr) := mul_le_mul_of_nonneg_left hT2 (by positivity)
  have hA : (((d₀ * q ^ n + M + d₁ * n * q ^ n * S₁ : ℕ) : ℝ)) * lδ ≤
      lδ * ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) * Mr := by
    have : (((d₀ * q ^ n + M + d₁ * n * q ^ n * S₁ : ℕ) : ℝ)) =
        d₀ * Tr + Mr + d₁ * n * S₁ * Tr := by
      rw [hTr, hMr]
      push_cast
      ring
    rw [this]
    have h1 : d₀ * Tr + Mr + d₁ * n * S₁ * Tr ≤ ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) * Mr := by
      have := mul_le_mul_of_nonneg_left hT2 (by positivity : (0 : ℝ) ≤ d₀ + d₁ * n * S₁)
      calc d₀ * Tr + Mr + d₁ * n * S₁ * Tr = (d₀ + d₁ * n * S₁) * Tr + Mr := by ring
        _ ≤ (d₀ + d₁ * n * S₁) * (2 * K₁ * Mr) + Mr := by linarith
        _ = ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) * Mr := by ring
    calc (d₀ * Tr + Mr + d₁ * n * S₁ * Tr) * lδ
        ≤ (((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) * Mr) * lδ := mul_le_mul_of_nonneg_right h1 hlδ0
      _ = lδ * ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) * Mr := by ring
  have hQ : (((d₀ * q ^ n : ℕ) : ℝ)) * Real.log ((δ : ℝ) ^ 2 * Mr + n * S₁ * Hg + 1) ≤
      d₀ * (2 * K₁) * (CQ + d) * Mr := by
    have hQle : Real.log ((δ : ℝ) ^ 2 * Mr + n * S₁ * Hg + 1) ≤ CQ + lM := by
      rw [hCQ, hlM, ← Real.log_mul (by positivity) hMpos.ne']
      refine Real.log_le_log (by positivity) ?_
      have : (0 : ℝ) ≤ n * S₁ * Hg + 1 := by positivity
      linarith [mul_le_mul_of_nonneg_left hM1 this]
    have hcast : (((d₀ * q ^ n : ℕ) : ℝ)) = d₀ * Tr := by rw [hTr]; push_cast; ring
    rw [hcast]
    have hlogQ0 : 0 ≤ Real.log ((δ : ℝ) ^ 2 * Mr + n * S₁ * Hg + 1) := by
      have : (0 : ℝ) ≤ (δ : ℝ) ^ 2 * Mr + n * S₁ * Hg := by positivity
      exact Real.log_nonneg (by linarith)
    calc d₀ * Tr * Real.log ((δ : ℝ) ^ 2 * Mr + n * S₁ * Hg + 1)
        ≤ d₀ * Tr * (CQ + lM) := mul_le_mul_of_nonneg_left hQle (by positivity)
      _ = d₀ * (Tr * CQ + Tr * lM) := by ring
      _ ≤ d₀ * (2 * K₁ * Mr * CQ + 2 * K₁ * d * Mr) := by
          gcongr
      _ = d₀ * (2 * K₁) * (CQ + d) * Mr := by ring
  have hW : Mr * Real.log (d₁ * Tr * Hg + 1) ≤ α * (Mr * lM) + (CW + α * lK) * Mr := by
    have hWle : d₁ * Tr * Hg + 1 ≤ (d₁ * Hg + 1) * τ := by
      have : (d₁ : ℝ) * Tr * Hg ≤ d₁ * τ * Hg := by gcongr
      linarith
    have hlogτ : Real.log τ = α * (lK + lM) := by
      rw [hτ, Real.log_rpow (by positivity), Real.log_mul (by positivity) hMpos.ne', hlK, hlM]
    have hlogW : Real.log (d₁ * Tr * Hg + 1) ≤ CW + α * (lK + lM) := by
      rw [← hlogτ, hCW, ← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) hWle
    calc Mr * Real.log (d₁ * Tr * Hg + 1) ≤ Mr * (CW + α * (lK + lM)) :=
          mul_le_mul_of_nonneg_left hlogW hMpos.le
      _ = α * (Mr * lM) + (CW + α * lK) * Mr := by ring
  have hH : (((d₁ * n * q ^ n * S₁ : ℕ) : ℝ)) * lH ≤ d₁ * n * S₁ * lH * (2 * K₁) * Mr := by
    have hcast : (((d₁ * n * q ^ n * S₁ : ℕ) : ℝ)) = d₁ * n * S₁ * Tr := by
      rw [hTr]; push_cast; ring
    rw [hcast]
    have := mul_le_mul_of_nonneg_left hT2 (by positivity : (0 : ℝ) ≤ d₁ * n * S₁ * lH)
    linarith
  have hlogn : Real.log n ≤ n * Mr := by
    have := log_le_self_of_nonneg (by positivity : (0 : ℝ) ≤ n)
    linarith [mul_le_mul_of_nonneg_left hM1 (by positivity : (0 : ℝ) ≤ n)]
  have hρ : (((d₀ * q ^ n : ℕ) : ℝ)) *
      Real.log (1 + Ay * (5 * 3 ^ n * Ep * (S₁ + 2 * B))) ≤ d₀ * (2 * K₁) * (Cr + d) * Mr := by
    have hρeq : Ay * (5 * 3 ^ n * Ep * (S₁ + 2 * B)) = Cρ * Ep := by rw [hCρ]; ring
    rw [hρeq]
    have hle : 1 + Cρ * Ep ≤ (1 + Cρ) * Ep := by linarith
    have hlog : Real.log (1 + Cρ * Ep) ≤ Cr + lM := by
      have h1 : Real.log (1 + Cρ * Ep) ≤ Cr + Real.log Ep := by
        rw [hCr, ← Real.log_mul (by positivity) (by positivity)]
        exact Real.log_le_log (by positivity) hle
      have h2 : Real.log Ep ≤ lM := by
        rw [hEp, Real.log_exp]
        exact div_le_self hlM0 hdR
      linarith
    have hcast : (((d₀ * q ^ n : ℕ) : ℝ)) = d₀ * Tr := by rw [hTr]; push_cast; ring
    rw [hcast]
    calc d₀ * Tr * Real.log (1 + Cρ * Ep) ≤ d₀ * Tr * (Cr + lM) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = d₀ * (Tr * Cr + Tr * lM) := by ring
      _ ≤ d₀ * (2 * K₁ * Mr * Cr + 2 * K₁ * d * Mr) := by
          gcongr
      _ = d₀ * (2 * K₁) * (Cr + d) * Mr := by ring
  have hTρ : Tr * Ax * (Ay * (5 * 3 ^ n * Ep * (S₁ + 2 * B))) ≤ 2 * K₁ * Ax * Cρ * Mr := by
    have hρeq : Ay * (5 * 3 ^ n * Ep * (S₁ + 2 * B)) = Cρ * Ep := by rw [hCρ]; ring
    rw [hρeq]
    have hTE : Tr * Ep ≤ 2 * K₁ * Mr := by
      calc Tr * Ep ≤ (2 * K₁ * Mr ^ α) * Mr ^ (1 / (d : ℝ)) := by
            rw [hEp_rpow]
            exact mul_le_mul_of_nonneg_right (hTτ.trans hτ_le) (by positivity)
        _ = 2 * K₁ * Mr ^ (α + 1 / d) := by rw [Real.rpow_add hMpos]; ring
        _ ≤ 2 * K₁ * Mr ^ (1 : ℝ) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hM1 hαd) (by positivity)
        _ = 2 * K₁ * Mr := by rw [Real.rpow_one]
    have := mul_le_mul_of_nonneg_left hTE (by positivity : (0 : ℝ) ≤ Ax * Cρ)
    linarith
  have hk : S₁ / (2 * n * d) * (Mr * lM) ≤ ((M / n * S₁ : ℕ) : ℝ) * (lM / d) := by
    have hMdiv : M ≤ 2 * n * (M / n) := by
      have h2 := Nat.mod_lt M (by omega : 0 < n)
      have h3 : 1 ≤ M / n := Nat.div_pos hMn (by omega)
      have h4 : n ≤ n * (M / n) := Nat.le_mul_of_pos_right _ h3
      calc M = n * (M / n) + M % n := (Nat.div_add_mod M n).symm
        _ ≤ n * (M / n) + n * (M / n) := by omega
        _ = 2 * n * (M / n) := by ring
    have hMdivR : Mr ≤ 2 * n * ((M / n : ℕ) : ℝ) := by rw [hMr]; exact_mod_cast hMdiv
    push_cast
    have hnpos : (0 : ℝ) < n := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hMdivR (by positivity : (0 : ℝ) ≤ S₁ * lM)
    have heq : ((M / n : ℕ) : ℝ) * S₁ * (lM / d) * (2 * n * d) =
        2 * n * ((M / n : ℕ) : ℝ) * (S₁ * lM) := by field_simp
    linarith
  have hS₁' : 2 + D * α + c₃ * K₁ / d ≤ S₁ / (2 * n * d) := by
    rw [le_div_iff₀ (by positivity), hα]
    have : (D : ℝ) * (n / d) = D * n / d := by ring
    rw [this]
    linarith
  -- assemble
  have hLF := liouvilleFactor_le_exp hD hδ hN0 hHg (d₀ := d₀) (d₁ := d₁) (n := n) (T := q ^ n)
    (S₁ := S₁) M
  set ρ : ℝ := Ay * (5 * 3 ^ n * Ep * (S₁ + 2 * B)) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hG := growth_eq (d₀ := d₀) (d₁ := d₁) (T := q ^ n) (N := Nq) (Ax := Ax) hρ0
  set k : ℕ := M / n * S₁ with hk_def
  have hpow : (1 / Ep) ^ k = Real.exp (-(k * (lM / d))) := by
    rw [hEp, one_div, ← Real.exp_neg, ← Real.exp_nat_mul]
    ring_nf
  have hnexp : (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log (by positivity)).symm
  have hphi : phiE d₀ d₁ n (q ^ n) S₁ δ D Nq Hg M = Mr * lM + D * (
      Real.log ((((q ^ n + 1) ^ d₀ * (q ^ n + 1) ^ d₁ : ℕ) : ℝ)) +
      (((d₀ * q ^ n + M + d₁ * n * q ^ n * S₁ : ℕ) : ℝ)) * lδ + Nq +
      (((d₀ * q ^ n : ℕ) : ℝ)) * Real.log ((δ : ℝ) ^ 2 * Mr + n * S₁ * Hg + 1) +
      Mr * Real.log (d₁ * Tr * Hg + 1) + (((d₁ * n * q ^ n * S₁ : ℕ) : ℝ)) * lH) := by
    unfold phiE
    simp only [hTr, Nat.cast_pow]
    rfl
  have hGexp : Real.log ((((q ^ n + 1) ^ d₀ * (q ^ n + 1) ^ d₁ : ℕ) : ℝ)) + Nq +
      (((d₀ * q ^ n : ℕ) : ℝ)) * Real.log (1 + ρ) + ((q ^ n : ℕ) : ℝ) * Ax * ρ =
      Real.log ((((q ^ n + 1) ^ d₀ * (q ^ n + 1) ^ d₁ : ℕ) : ℝ)) + Nq +
      (((d₀ * q ^ n : ℕ) : ℝ)) * Real.log (1 + ρ) + Tr * Ax * ρ := by
    rw [hTr, Nat.cast_pow]
  set Ex : ℝ := phiE d₀ d₁ n (q ^ n) S₁ δ D Nq Hg M + Real.log n + -(k * (lM / d)) +
    (Real.log ((((q ^ n + 1) ^ d₀ * (q ^ n + 1) ^ d₁ : ℕ) : ℝ)) + Nq +
      (((d₀ * q ^ n : ℕ) : ℝ)) * Real.log (1 + ρ) + ((q ^ n : ℕ) : ℝ) * Ax * ρ) with hEx
  have hExneg : Ex < 0 := by
    rw [hEx, hphi, hGexp]
    have hkM := hk
    rw [hk_def] at hkM
    have hMl := mul_le_mul_of_nonneg_left hlMC hMpos.le
    have hC₇M : Mr * C₇ = Mr * (D * d * (2 * K₁) + D * lδ * ((d₀ + d₁ * n * S₁) * (2 * K₁) + 1) +
        c₃ * K₁ / d * lK + D * d₀ * (2 * K₁) * (CQ + d) + D * (CW + α * lK) +
        D * d₁ * n * S₁ * lH * (2 * K₁) + n + d * (2 * K₁) + d₀ * (2 * K₁) * (Cr + d) +
        2 * K₁ * Ax * Cρ) := by rw [hC₇]
    have hS₁M := mul_le_mul_of_nonneg_right hS₁' (by positivity : (0 : ℝ) ≤ Mr * lM)
    have hD0 : (0 : ℝ) ≤ D := by linarith
    have e1 := mul_le_mul_of_nonneg_left hc hD0
    have e2 := mul_le_mul_of_nonneg_left hA hD0
    have e3 := mul_le_mul_of_nonneg_left hQ hD0
    have e4 := mul_le_mul_of_nonneg_left hW hD0
    have e5 := mul_le_mul_of_nonneg_left hH hD0
    have hαM : D * (α * (Mr * lM)) = D * α * (Mr * lM) := by ring
    exact exponent_lt_zero hMpos e1 e2 hDN e3 e4 e5 hlogn hkM hc hN1 hρ hTρ hS₁M hMl hC₇
  have hfac : 0 ≤ (n : ℝ) * (1 / Ep) ^ k * growth d₀ d₁ (q ^ n) Nq Ax ρ := by
    rw [hG]
    positivity
  calc liouvilleFactor d₀ d₁ n (q ^ n) S₁ δ D Nq Hg M *
        ((n : ℝ) * (1 / Ep) ^ k * growth d₀ d₁ (q ^ n) Nq Ax ρ)
      ≤ Real.exp (phiE d₀ d₁ n (q ^ n) S₁ δ D Nq Hg M) *
        ((n : ℝ) * (1 / Ep) ^ k * growth d₀ d₁ (q ^ n) Nq Ax ρ) :=
        mul_le_mul_of_nonneg_right hLF hfac
    _ = Real.exp Ex := by
        rw [hpow, hG, hEx]
        conv_lhs => rw [hnexp]
        simp only [← Real.exp_add]
        congr 1
        ring
    _ < 1 := Real.exp_lt_one_iff.2 hExneg

/-- **The choice of parameters** (step 6 of §4.6 of [waldschmidt2000]).  For fixed data there
are parameters satisfying all the inequalities used in `core`. -/
theorem exists_parameters (hn1 : 1 ≤ n) (hd : n < d₀ + d₁) {D δ : ℕ} (hD : 1 ≤ D)
    (hδ : 1 ≤ δ) {Hg Ax Ay B : ℝ} (hHg : 1 ≤ Hg) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay) (hB : 0 ≤ B) :
    ∃ (T S₁ S₀ : ℕ) (U N r : ℝ) (R : NNReal) (Ep : ℕ → ℝ),
      1 ≤ S₁ ∧ 0 < N ∧ 0 < r ∧ S₁ * Ay + 2 ≤ r ∧ 12 * (n : ℝ) ^ 2 ≤ N + U + U ∧
      Real.exp 1 ≤ R / r ∧ R / r ≤ Real.exp ((N + U + U) / 6) ∧
      (2 * (N + U + U)) ^ (n + 1) ≤
        ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * N * Real.log (R / r) ^ n ∧
      ((T + 1) ^ d₀ * (T + 1) ^ d₁ : ℕ) * ((1 + (R : ℝ)) ^ (d₀ * T) *
        Real.exp (T * Ax * R)) ≤ Real.exp U ∧
      (∀ M : ℕ, M ≤ n * S₀ → liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M * Real.exp (-U) < 1) ∧
      (∀ M, 1 ≤ Ep M) ∧
      (∀ M : ℕ, S₀ ≤ M → liouvilleFactor d₀ d₁ n T S₁ δ D N Hg M *
        (n * (1 / Ep M) ^ (M / n * S₁) * growth d₀ d₁ T N Ax
          (Ay * (5 * 3 ^ n * Ep M * (S₁ + 2 * B)))) < 1) := by
  sorry

/-- **Corollary 4.2 of [waldschmidt2000]**, proved. -/
theorem main (hd₀ : d₀ ≤ n) (hn : n < d₀ + d₁)
    (x : Fin d₁ → Fin n → ℂ) (hx : ∀ i v, IsAlgebraic ℚ (x i v))
    (hxli : LinearIndependent ℚ x)
    (y : Fin n → Fin n → ℂ) (hyli : LinearIndependent ℂ y) :
    (∃ (h : Fin d₀) (j : Fin n), Transcendental ℚ (y j (Fin.castLE hd₀ h))) ∨
      ∃ (i : Fin d₁) (j : Fin n), Transcendental ℚ (Complex.exp (∑ v, x i v * y j v)) := by
  classical
  by_contra hcon
  simp only [not_or, not_exists, Transcendental, not_not] at hcon
  obtain ⟨hyalg, hexpalg⟩ := hcon
  -- `n ≥ 1`
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hxli.ne_zero ⟨0, by omega⟩ (funext fun v => v.elim0)
  -- the change of variables `z ↦ ∑ⱼ zⱼ yⱼ`
  set Lm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Fintype.linearCombination ℂ y with hLm
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    funext j
    exact Fintype.linearIndependent_iff.1 hyli z
      (by simpa [hLm, Fintype.linearCombination_apply] using hz) j
  set Yl := (LinearEquiv.ofInjectiveEndo Lm hinj).toContinuousLinearEquiv with hYldef
  have hYl : ∀ z, Yl z = fun v => ∑ j, z j * y j v := fun z => by
    funext v
    simp [hYldef, hLm, Fintype.linearCombination_apply, Finset.sum_apply]
  -- the number field generated by the data
  set S : Set ℂ := Set.range (fun p : Fin d₁ × Fin n => x p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin d₀ => y p.1 (Fin.castLE hd₀ p.2)) ∪
    Set.range (fun p : Fin d₁ × Fin n => Complex.exp (∑ v, x p.1 v * y p.2 v)) with hS
  have hSfin : S.Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)
  have : Finite S := hSfin.to_subtype
  have hSalg : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    rcases hz with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
    · exact hx _ _
    · exact hyalg _ _
    · exact hexpalg _ _
  set K := IntermediateField.adjoin ℚ S with hK
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hSalg z hz).isIntegral
  have : NumberField K := ⟨⟩
  have hmem : ∀ z ∈ S, z ∈ K := fun z hz => IntermediateField.subset_adjoin ℚ S hz
  set X : Fin d₁ → Fin n → K := fun i v => ⟨x i v, hmem _ (by simp [hS])⟩ with hXdef
  set Yg : Fin n → Fin d₀ → K := fun j h => ⟨y j (Fin.castLE hd₀ h), hmem _ (by
    refine Or.inl (Or.inr ⟨(j, h), rfl⟩))⟩ with hYgdef
  set Eg : Fin d₁ → Fin n → K := fun i j => ⟨Complex.exp (∑ v, x i v * y j v), hmem _ (by
    exact Or.inr ⟨(i, j), rfl⟩)⟩ with hEgdef
  set ι₀ : K →+* ℂ := (IntermediateField.val K).toRingHom with hι₀
  have hX : ∀ i v, ι₀ (X i v) = x i v := fun i v => rfl
  have hY : ∀ j (v : Fin n) (h : (v : ℕ) < d₀), ι₀ (Yg j ⟨v, h⟩) = y j v := fun j v h => rfl
  have hE : ∀ i j, ι₀ (Eg i j) = Complex.exp (∑ v, x i v * y j v) := fun i j => rfl
  -- a common denominator and a bound for the houses
  set gens : Finset K := (Finset.univ.image fun p : Fin d₁ × Fin n => X p.1 p.2) ∪
    (Finset.univ.image fun p : Fin n × Fin d₀ => Yg p.1 p.2) ∪
    (Finset.univ.image fun p : Fin d₁ × Fin n => Eg p.1 p.2) with hgens
  obtain ⟨c, hc0, hc⟩ := exists_integral_multiples ℤ ℚ (L := K) gens
  set δ : ℕ := c.natAbs with hδdef
  have hδ : 1 ≤ δ := Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hc0)
  have hint : ∀ g ∈ gens, IsIntegral ℤ ((δ : K) ^ 1 * g) := by
    intro g hg
    have h1 := hc g hg
    rw [pow_one]
    rcases Int.natAbs_eq c with h | h
    · have : (δ : K) * g = c • g := by
        rw [zsmul_eq_mul, hδdef,
          show ((c.natAbs : ℕ) : K) = (((c.natAbs : ℕ) : ℤ) : K) from (Int.cast_natCast _).symm,
          ← h]
      rw [this]
      exact h1
    · have : (δ : K) * g = -(c • g) := by
        rw [zsmul_eq_mul, hδdef, ← neg_mul,
          show ((c.natAbs : ℕ) : K) = (((c.natAbs : ℕ) : ℤ) : K) from (Int.cast_natCast _).symm,
          show ((c.natAbs : ℕ) : ℤ) = -c by omega, Int.cast_neg]
      rw [this]
      exact h1.neg
  set Hg : ℝ := 1 + ∑ g ∈ gens, house ((δ : K) ^ 1 * g) with hHgdef
  have hHg : 1 ≤ Hg := by
    have : 0 ≤ ∑ g ∈ gens, house ((δ : K) ^ 1 * g) := Finset.sum_nonneg fun g _ => house_nonneg _
    linarith
  have hsize : ∀ g ∈ gens, AlgSize δ g 1 Hg := fun g hg => ⟨hint g hg, by
    rw [hHgdef]
    have := Finset.single_le_sum (fun g _ => house_nonneg ((δ : K) ^ 1 * g)) hg
    linarith⟩
  have hXs : ∀ i v, AlgSize δ (X i v) 1 Hg := fun i v =>
    hsize _ (by simp [hgens])
  have hYs : ∀ j h, AlgSize δ (Yg j h) 1 Hg := fun j h =>
    hsize _ (by simp [hgens])
  have hEs : ∀ i j, AlgSize δ (Eg i j) 1 Hg := fun i j =>
    hsize _ (by simp [hgens])
  have hD : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  -- the parameters, and the contradiction
  obtain ⟨T, S₁, S₀, U, N, r, R, Ep, hS₁, hN, hr0, hr, hW, hRr, hRr', hL, hMU, hvan, hEp,
    hbig⟩ := exists_parameters hn1 hn hD hδ hHg (Ax := ∑ i, ∑ v, ‖x i v‖)
      (Ay := ∑ j, ∑ v, ‖y j v‖)
      (B := ‖(Yl.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖) (by positivity) (by positivity)
      (norm_nonneg _)
  exact core hn1 hd₀ hxli Yl hYl ι₀ hX hY hE hδ hHg hXs hYs hEs T S₁ S₀ hS₁ hN hr0 hr hW hRr
    hRr' hL hMU hvan Ep hEp hbig

end Transcendental.SchneiderLangProof
