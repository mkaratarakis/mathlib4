/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainOrder
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.AnalyticPart

/-! The goal of this file is to establish the critical lower bound for the proof of the
Gelfond-Schneider Theorem. Having constructed an auxiliary exponential polynomial
`R(x)` that vanishes to high order at specific points, we now isolate the first non-vanishing
derivative of `R(x)` and use its algebraic properties to bound it away from zero.

## Main Objective

To derive a contradiction, we need two opposing bounds on the size of the derivatives of `R(x)`.
This file is entirely dedicated to constructing the lower bound.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

lemma iteratedkDeriv_R_eq_zero (k : Fin (h7.n q)) (l' : Fin (h7.m)) :
    deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
  let u : Fin (h7.m * h7.n q) := (finProdFinEquiv.toFun ⟨l',k⟩)
  have h1 := coeffs_mul_deriv_eq_zero h7 q hq0 u h2mq
  unfold Setup.k at *
  unfold Setup.l at *
  unfold u at *
  simp only [Equiv.toFun_as_coe,
    Equiv.symm_apply_apply] at *
  have : (h7.σ (h7.c_coeffs q) *
   (Complex.log h7.α)^(-k : ℤ)) * deriv^[k] (h7.R q hq0 h2mq) (l'+1) =
    (h7.σ (h7.c_coeffs q) *
    (Complex.log h7.α)^(-k : ℤ)) * 0 → deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
      apply mul_left_cancel₀
      by_contra H
      simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow,
        map_intCast, zpow_neg, zpow_natCast,
        mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or, inv_eq_zero] at H
      rcases H with ⟨h1, h2⟩
      · apply h7.c₁_ne_zero; assumption
      ·  apply h7.c₁_ne_zero; rename_i h2; exact h2.1
      · apply h7.c₁_ne_zero; rename_i h2; exact h2.1
      · have : Complex.log h7.α ≠ 0 :=
         mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2
        apply this; rename_i h2; exact h2.1
  rw [this]
  rw [mul_zero]
  rw [mul_assoc]
  simp only [mul_assoc] at *
  rw [← h1]
  simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg, zpow_natCast,
    Nat.cast_add, Nat.cast_one]

lemma order_neq_top : ∀ (l' : Fin (h7.m)), analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply h7.R_ne_zero q hq0 h2mq (by aesop)
  fun_prop

lemma order_neq_top_min_one : ∀ z : ℂ, analyticOrderAt (h7.R q hq0 h2mq) z ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply h7.R_ne_zero
    · rw [funext_iff]
      intros z
      rw [funext_iff] at H
      apply H z
  intros z
  fun_prop

lemma Rorder_exists (z : ℂ) :
    ∃ r, (analyticOrderAt (h7.R q hq0 h2mq) z) = some r := by
  have : (analyticOrderAt (h7.R q hq0 h2mq) z) ≠ ⊤ :=
    h7.order_neq_top_min_one q hq0 h2mq z
  revert this
  cases (analyticOrderAt (h7.R q hq0 h2mq) z) with
  | top => grind
  | coe => aesop

def R_order (z : ℂ) : ℕ := (Rorder_exists h7 q hq0 h2mq z).choose

def R_order_prop {z : ℂ} := (Rorder_exists h7 q hq0 h2mq z).choose_spec

lemma R_order_eq (z) : (analyticOrderAt (h7.R q hq0 h2mq) z) = h7.R_order q hq0 h2mq z :=
  (Rorder_exists h7 q hq0 h2mq z).choose_spec

lemma r_exists : ∃ r, r' h7 q hq0 h2mq = some r := by
  have H := order_neq_top_min_one h7 q hq0 h2mq (l₀' h7 q hq0 h2mq + 1)
  have : r' h7 q hq0 h2mq ≠ ⊤ := by rw [(r'_prop h7 q hq0 h2mq).1] at H; exact H
  revert this
  cases r' h7 q hq0 h2mq with
  | top => grind
  | coe => aesop

def r := (r_exists h7 q hq0 h2mq).choose

abbrev r_spec : h7.r' q hq0 h2mq = ↑(h7.r q hq0 h2mq) :=
  (r_exists h7 q hq0 h2mq).choose_spec

abbrev r_prop :
  let s : Finset (Fin (h7.m)) := Finset.univ
  analyticOrderAt (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) = h7.r q hq0 h2mq ∧
  ∀ l' ∈ s, h7.r q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' + 1) := by
  intros s
  rw [← h7.r_spec q hq0 h2mq]
  apply h7.r'_prop q hq0 h2mq

lemma r_div_q_geq_0 : 0 ≤ (h7.r q hq0 h2mq) / q := by simp_all only [zero_le]

lemma order_geq_n_foo (l' : Fin (h7.m)) :
  (∀ k', k' < h7.n q → deriv^[k'] (h7.R q hq0 h2mq) (l' + 1) = 0)
   → h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros H
  apply le_analyticOrderAt_iff_iteratedDeriv_eq_zero
  · fun_prop
  · apply order_neq_top h7 q hq0 h2mq l'
  exact H

lemma order_geq_n : ∀ l' : Fin (h7.m),
    h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros l'
  apply order_geq_n_foo
  intros k hk
  have H := h7.iteratedkDeriv_R_eq_zero q hq0 h2mq ⟨k,hk⟩ l'
  rw [H]

lemma n_le_r : h7.n q ≤ h7.r q hq0 h2mq := by
  have := h7.r_prop q hq0 h2mq
  obtain ⟨hr,hprop⟩ := this
  have := h7.order_geq_n q hq0 h2mq (h7.l₀' q hq0 h2mq)
  have H : h7.n q ≤ (h7.r q hq0 h2mq : ℕ∞) → h7.n q ≤ h7.r q hq0 h2mq := by
    simp only [Nat.cast_le, imp_self]
  apply H
  rw [← hr]
  apply this

lemma r_ne_zero : h7.r q hq0 h2mq ≠ 0 := by
  have H := n_le_r h7 q hq0 h2mq
  have : 0 < h7.n q := by
    unfold n; simp only [Nat.div_pos_iff, Nat.ofNat_pos,
    mul_pos_iff_of_pos_left]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩
  aesop

def cρ : ℤ := abs (h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁^(2*h7.m * q))

abbrev systemCoeffs_r : h7.K := (a q t + b q t • h7.β')^(h7.r q hq0 h2mq) *
 h7.α' ^(a q t * (h7.l₀' q hq0 h2mq + 1)) * h7.γ' ^(b q t * (h7.l₀' q hq0 h2mq + 1))

lemma systemCoeffs_ne_zero_r : h7.systemCoeffs_r q hq0 t h2mq ≠ 0 := by
  unfold systemCoeffs_r
  intros H
  simp only [mul_eq_zero, pow_eq_zero_iff'] at H
  cases H with
  | inl H1 =>
    cases H1 with
    | inl H1 =>
      rcases H1 with ⟨h1, h2⟩
      apply (h7.β'_ne_zero q t (h7.r q hq0 h2mq))
      rw [h1]
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact h2
    | inr H2 => exact h7.alpha'_beta'_gamma'_ne_zero.1 H2.1
  | inr H2 =>
    exfalso
    exact h7.alpha'_beta'_gamma'_ne_zero.2.2 H2.1

def ρᵣ : ℂ := (Complex.log h7.α)^(-(h7.r q hq0 h2mq) : ℤ) *
 deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1)

lemma systemCoeffs_bar_r :
  exp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) *
  h7.ρ q t ^ (h7.r q hq0 h2mq : ℕ) *
  Complex.log h7.α ^ (-(h7.r q hq0 h2mq) : ℤ) = h7.σ (h7.systemCoeffs_r q hq0 t h2mq) := by
    nth_rw 2 [ρ]
    rw [mul_pow, mul_assoc, mul_assoc]
    have : (Complex.log h7.α ^ (h7.r q hq0 h2mq : ℕ) *
      Complex.log h7.α ^ (-h7.r q hq0 h2mq : ℤ)) = 1 := by
      simp only [zpow_neg, zpow_natCast]
      refine Complex.mul_inv_cancel ?_
      by_contra! H
      have : Complex.log h7.α ≠ 0 :=
         mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2
      apply this
      simp only [pow_eq_zero_iff', ne_eq] at H
      apply H.1
    rw [this]; clear this
    rw [mul_one]
    unfold systemCoeffs_r
    rw [mul_comm]
    change _ = h7.σ ((↑(a q t) + b q t • h7.β') ^ (h7.r q hq0 h2mq : ℕ)
      * (h7.α' ^ (a q t * (h7.l₀' q hq0 h2mq + 1))) * (h7.γ' ^ (b q t * (h7.l₀' q hq0 h2mq + 1))))
    rw [map_mul]
    rw [map_mul]
    nth_rw 1 [mul_assoc]
    have : h7.σ ((↑(a q t) + (b q t) • h7.β') ^ (h7.r q hq0 h2mq)) =
        (↑(a q t) + ↑(b q t) * h7.β) ^ ((h7.r q hq0 h2mq)) := by
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [a, b]
      congr
      rw [h7.habc.2.1]
    rw [this]; clear this
    rw [map_pow, map_pow]
    have : (↑(a q t) + (b q t) • h7.β) ^
      (h7.r q hq0 h2mq) * cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) =
        (↑(a q t) + ↑(b q t) * h7.β)^(h7.r q hq0 h2mq) *
          cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) := by
      simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_modNat,
        Fin.coe_divNat, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,b, a]
    rw [this]; clear this
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff']
    left
    rw [ρ]
    have : cexp (( ↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1)
        ) =
        cexp ((↑(a q t) + ↑(b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq +1)) := by
          simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
          Fin.coe_modNat,
            Fin.coe_divNat, Nat.cast_add, Nat.cast_one,
            nsmul_eq_mul, b, a]
    rw [this];clear this
    have : h7.σ h7.α' ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
       h7.σ h7.γ' ^ ((b q t) * (h7.l₀' q hq0 h2mq + 1)) =
       h7.α ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
       (h7.σ h7.γ')^ ((b q t) * (h7.l₀' q hq0 h2mq + 1)) := by
      simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
        map_eq_zero, ne_eq, mul_eq_zero, not_or]
      left
      congr
      rw [← h7.habc.1]
    rw [← h7.habc.1]
    have : h7.σ h7.γ' = h7.α^h7.β := by rw [h7.habc.2.2]
    rw [this]; clear this
    have : Complex.exp (Complex.log h7.α) = h7.α :=
      Complex.exp_log h7.htriv.1
    clear this
    rw [← cpow_nat_mul]
    have : cexp ((↑(a q t) + (b q t) • h7.β) *
      Complex.log h7.α * (h7.l₀' q hq0 h2mq +1)) =
        h7.α ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
        h7.α ^ (↑((b q t) * (h7.l₀' q hq0 h2mq +1 )) * h7.β) ↔
      cexp ((↑(a q t) + (b q t) • h7.β) *
      Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1)) =
        h7.α ^ (((a q t) * (h7.l₀' q hq0 h2mq +1)) +
         ((↑(b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β)) := by
        rw [cpow_add]
        · simp only [nsmul_eq_mul, Nat.cast_mul]
          norm_cast
        exact h7.htriv.1
    rw [this]; clear this
    rw [cpow_def_of_ne_zero]
    · have : Complex.log h7.α * (↑(a q t) * (h7.l₀' q hq0 h2mq +1) +
       ((b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β) =
        (↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1) := by
        nth_rw 4 [mul_comm]
        have : ( ((h7.l₀' q hq0 h2mq + 1) * (b q t)) * h7.β) =
        ( (((b q t) * h7.β) * (h7.l₀' q hq0 h2mq + 1))) := by
          exact mul_rotate (↑↑(h7.l₀' q hq0 h2mq) + 1) (↑(b q t)) h7.β
        rw [this];clear this
        have H : (↑(a q t) * (h7.l₀' q hq0 h2mq + 1) +
        (((b q t) * h7.β) * (h7.l₀' q hq0 h2mq +1))) =
        (((a q t)  + ((b q t) * h7.β)) *  ↑((↑(h7.l₀' q hq0 h2mq : ℕ) + 1  :ℂ))) :=
        Eq.symm (RightDistribClass.right_distrib
          (↑(a q t)) (↑(b q t) * h7.β) (h7.l₀' q hq0 h2mq + 1))
        rw [H, mul_comm, mul_assoc]
        nth_rw 3 [mul_comm]
        rw [← mul_assoc, nsmul_eq_mul]
      rw [this]
    · exact h7.htriv.1

def deriv_R_k_eval_at_l0' :
  deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
  ∑ t, h7.σ ((h7.η q hq0 h2mq) t) *
  cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) * (h7.ρ q t) ^ (h7.r q hq0 h2mq) := by
  rw [iteratedDeriv_R]

lemma systemCoeffs_deriv_r :
 (Complex.log h7.α)^(-h7.r q hq0 h2mq : ℤ) * deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
 ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.systemCoeffs_r q hq0 t h2mq) := by
  rw [h7.deriv_R_k_eval_at_l0' q hq0 h2mq, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  unfold η
  simp only [mul_eq_mul_left_iff, map_eq_zero,
    FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := systemCoeffs_bar_r h7 q hq0 t h2mq
  rw [← this]

def rho := ∑ t : Fin (q * q), (h7.η q hq0 h2mq t) * (h7.systemCoeffs_r q hq0 t h2mq)

def rho_eq_ρᵣ : h7.σ (rho h7 q hq0 h2mq) = ρᵣ h7 q hq0 h2mq := by
  unfold rho ρᵣ
  rw [systemCoeffs_deriv_r]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]

lemma exists_nonzero_iteratedFDeriv : deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) ≠ 0 := by
  have Hrprop := (h7.r_prop q hq0 h2mq).1
  obtain ⟨l₀, y, r, h1, h2⟩ :=
    (h7.exists_min_analyticOrderAt q hq0 h2mq)
  have hA1 := h7.R_analyt_at_point q hq0 h2mq (h7.l₀' q hq0 h2mq + 1)
  grind [analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero hA1]

lemma ρᵣ_nonzero : ρᵣ h7 q hq0 h2mq ≠ 0 := by
  unfold ρᵣ
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  refine ⟨fun hlog => ?_, h7.exists_nonzero_iteratedFDeriv q hq0 h2mq⟩
  · by_contra H
    have : Complex.log h7.α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2
    apply this; exact hlog

lemma cρ_ne_zero : h7.cρ q hq0 h2mq ≠ 0 := by
  apply abs_ne_zero.mpr <| mul_ne_zero _ _
  all_goals apply pow_ne_zero _ (h7.c₁_ne_zero)

/-!
This number lies in $K,$ and ${c_1}^{r+2mq}\rho$ is an integer in $K$
-/

lemma ρ_is_int :
  IsIntegral ℤ (h7.cρ q hq0 h2mq • rho h7 q hq0 h2mq) := by
  unfold rho cρ systemCoeffs_r
  have : h7.c₁ ^ (2 * h7.m * q) = h7.c₁ ^ (h7.m * q)
  * h7.c₁ ^ (h7.m * q) := by
      rw [← pow_add]; ring
  rw [this]
  rcases abs_choice (h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) with H1 | H2
  · rw [← mul_assoc, H1, Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    · rw [mul_comm, ← zsmul_eq_mul]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      have := triple_comm h7.K
        (h7.c₁^(h7.r q hq0 h2mq) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (((a q x : ℕ) + b q x • h7.β')^(h7.r q hq0 h2mq))
        (h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)))
        (h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))
      have : IsIntegral ℤ
         ((h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) •
        ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
          h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
          h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) =
       IsIntegral ℤ
         (h7.c₁ ^ (h7.r q hq0 h2mq) • (↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
          h7.c₁ ^ (h7.m * q) • h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
          h7.c₁ ^ (h7.m * q) • h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1))) := by
        rw [← this]
      simp_rw [this]
      apply IsIntegral.mul
      · apply IsIntegral.mul
        · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
          rw [← mul_pow]
          apply IsIntegral.pow
          rw [mul_add]
          apply IsIntegral.add
          · apply IsIntegral.mul <| IsIntegral.Cast _ _
            · apply IsIntegral.Nat
          · rw [mul_comm, mul_assoc]
            apply IsIntegral.mul
            · apply IsIntegral.Nat
            · rw [mul_comm];
              have := h7.isIntegral_c₁β
              simp only [zsmul_eq_mul] at this
              exact this
        · apply h7.isIntegral_c₁_pow_smul_pow
          · rw [mul_comm]
            apply Nat.mul_le_mul ((h7.l₀' q hq0 h2mq).isLt) ((finProdFinEquiv.symm.toFun x).1.isLt)
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α
      · have : h7.c₁ ^ (h7.m * q - ((b q x) * (h7.l₀' q hq0 h2mq + 1))) *
           (h7.c₁ ^ ((b q x) * (h7.l₀' q hq0 h2mq + 1))) =
              (h7.c₁ ^ ((h7.m * q))) := by
          rw [← pow_add,Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact (h7.l₀' q hq0 h2mq).isLt
          · exact (finProdFinEquiv.symm.toFun x).2.isLt
          · simp only [zero_le]
          · simp only [zero_le]
        rw [← this]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
        rw [mul_assoc]
        apply IsIntegral.mul
        · apply IsIntegral.pow
          · apply IsIntegral.Cast
        · rw [← mul_pow]
          apply IsIntegral.pow
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ
  · rw [Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [← mul_assoc, H2]
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    · rw [mul_comm]
      rw [← zsmul_eq_mul]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      have H := triple_comm h7.K
        (h7.c₁^(h7.r q hq0 h2mq))
        (h7.c₁^(h7.m * q) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (((a q x : ℕ) + (b q x) • h7.β')^(h7.r q hq0 h2mq))
        (h7.α' ^ ((a q x) * ((h7.l₀' q hq0 h2mq + 1))))
        (h7.γ' ^ ((b q x) * ((h7.l₀' q hq0 h2mq + 1))))
      have : IsIntegral ℤ (-(h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) •
    ((↑(a q x) + b q x • h7.β') ^ h7.r q hq0 h2mq * h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
      h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) =
         IsIntegral ℤ ((h7.c₁ ^ (h7.r q hq0 h2mq) •
          (↑(a q x) + (b q x) • h7.β') ^ (h7.r q hq0 h2mq)
           * h7.c₁ ^ (h7.m * q) • h7.α' ^ ((a q x) *
           (h7.l₀' q hq0 h2mq + 1)) * h7.c₁ ^ (h7.m * q) •
             h7.γ' ^ ((b q x) * (h7.l₀' q hq0 h2mq + 1)))) := by
          rw [← H]
          rw [neg_smul]
          simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
            IsIntegral.neg_iff]
      clear H
      rw [this]
      apply IsIntegral.mul
      · apply IsIntegral.mul
        · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
          rw [← mul_pow]
          apply IsIntegral.pow
          rw [mul_add]
          · apply IsIntegral.add
            · apply IsIntegral.mul <| IsIntegral.Cast _ _
              · apply IsIntegral.Nat
            ·rw [mul_comm, mul_assoc]
             apply IsIntegral.mul <| IsIntegral.Nat _ _
             rw [mul_comm, ← zsmul_eq_mul]
             exact h7.isIntegral_c₁β
        · apply h7.isIntegral_c₁_pow_smul_pow
          · rw [mul_comm]
            apply Nat.mul_le_mul
            · exact (h7.l₀' q hq0 h2mq).isLt
            exact (finProdFinEquiv.symm.toFun x).1.isLt
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α
      · have : h7.c₁ ^ (h7.m * q - (b q x * (h7.l₀' q hq0 h2mq + 1))) *
           (h7.c₁ ^ ((b q x) * (h7.l₀' q hq0 h2mq + 1))) = (h7.c₁ ^ ((h7.m * q))) := by
          rw [← pow_add, Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact (h7.l₀' q hq0 h2mq).isLt
          · exact (finProdFinEquiv.symm.toFun x).2.isLt
          · simp only [zero_le]
          · simp only [zero_le]
        rw [← this]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
        rw [mul_assoc]
        apply IsIntegral.mul
        · apply IsIntegral.pow
          · apply IsIntegral.Cast
        · rw [← mul_pow]
          apply IsIntegral.pow
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

def c1ρ : 𝓞 h7.K := RingOfIntegers.restrict _
  (fun _ => (ρ_is_int h7 q hq0 h2mq)) ℤ

lemma one_le_c1rho : 1 ≤ ↑(h7.cρ q hq0 h2mq) := by
  apply Int.one_le_abs
  by_contra H
  simp only [mul_eq_zero, pow_eq_zero_iff', ne_eq,
    OfNat.ofNat_ne_zero, false_or, not_or] at H
  cases H with
  | inl h1 => apply (h7.c₁_ne_zero); exact h1.1
  | inr h2 => apply (h7.c₁_ne_zero); exact h2.1

lemma one_le_norm_c1rho : 1 ≤ norm (h7.cρ q hq0 h2mq) := by
  have := one_le_c1rho h7 q hq0 h2mq
  have : |(h7.cρ q hq0 h2mq)| = ‖(h7.cρ q hq0 h2mq : ℤ)‖ := by
    simp only [Int.cast_abs]
    exact rfl
  rw [← this]
  simp only [Int.cast_abs, ge_iff_le]
  have := Int.one_le_abs (z := h7.cρ q hq0 h2mq)
  norm_cast
  apply this
  exact cρ_ne_zero h7 q hq0 h2mq

lemma zero_le_c1rho : 0 ≤ ↑(h7.cρ q hq0 h2mq) :=
  Int.le_of_lt (one_le_c1rho h7 q hq0 h2mq)

lemma crho_le_abs_crho :
    (h7.cρ q hq0 h2mq) ≤ abs (h7.cρ q hq0 h2mq):= le_abs_self _

lemma abs_crho_le_norm_crho :
    abs (h7.cρ q hq0 h2mq) ≤ norm (h7.cρ q hq0 h2mq) := by
  simp only [Int.cast_abs]
  rfl

lemma norm_crho_le_house_crho : norm (h7.cρ q hq0 h2mq) ≤
  house (h7.cρ q hq0 h2mq : h7.K) := by
  rw [house_intCast]
  simp only [Int.cast_abs]
  exact Preorder.le_refl ‖h7.cρ q hq0 h2mq‖

lemma norm_cρ_pos : 0 < ‖h7.cρ q hq0 h2mq‖ := by
  rw [norm_pos_iff]
  have := h7.cρ_ne_zero q hq0 h2mq
  unfold cρ at this
  exact this

lemma h1 : 1 ≤ ‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K := by
      rw [one_le_pow_iff_of_nonneg]
      · rw [Int.norm_eq_abs]
        have := (h7.norm_cρ_pos q hq0 h2mq)
        rw [Int.norm_eq_abs] at this
        unfold cρ
        simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
        rw [← pow_add]
        simp only [abs_pow]
        have : 1 ≤ |↑(h7.c₁)| := by
          rw [le_abs']
          right
          exact h7.one_le_c₁
        refine one_le_pow₀ ?_
        exact mod_cast this
      · apply norm_nonneg
      · have : 0 < Module.finrank ℚ h7.K  := Module.finrank_pos
        simp_all only [ne_eq]
        intro a
        simp_all only [lt_self_iff_false]

lemma rho_nonzero : rho h7 q hq0 h2mq ≠ 0 := by
  intros H
  apply_fun h7.σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply h7.ρᵣ_nonzero
  exact H

lemma norm_Algebra_norm_rho_nonzero :
  ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ ≠ 0 := by
  rw [norm_ne_zero_iff, Algebra.norm_ne_zero_iff]
  intros H
  apply_fun h7.σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply ρᵣ_nonzero h7 q hq0 h2mq
  exact H

lemma c1rho_neq_0 : h7.c1ρ q hq0 h2mq ≠ 0 := by
  intros H
  injection H with H1
  simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H1
  cases H1 with
  | inl hp => apply cρ_ne_zero h7 q hq0 h2mq; exact hp
  | inr hq =>
    apply_fun h7.σ at hq
    rw [rho_eq_ρᵣ] at hq
    simp only [map_zero] at hq
    apply ρᵣ_nonzero h7 q hq0 h2mq
    exact hq

lemma house_geq_1 : 1 ≤ house (h7.c1ρ q hq0 h2mq : h7.K) := by
  apply one_le_house_of_isIntegral (RingOfIntegers.isIntegral_coe (h7.c1ρ q hq0 h2mq))
  simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← ne_eq]
  exact c1rho_neq_0 h7 q hq0 h2mq

lemma eq5zero : 1 ≤ norm
    (Algebra.norm ℚ ((algebraMap (𝓞 h7.K) h7.K) (h7.c1ρ q hq0 h2mq))) := by
  have := ρ_is_int h7 q hq0 h2mq
  have := Algebra.isIntegral_norm ℚ this
  have H1 : 0 ≤ ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    positivity
  have H2 : 0 ≠ ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    have := c1rho_neq_0 h7 q hq0 h2mq
    symm
    intros H
    apply this
    rw [norm_eq_zero] at H
    simp only [Algebra.norm_eq_zero_iff] at H
    exact H
  have : 0 < ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    exact lt_of_le_of_ne H1 H2
  rw [← Algebra.coe_norm_int] at *
  simp only [Int.norm_cast_rat, ge_iff_le] at *
  rw [← Int.norm_cast_real] at *
  simp only [Real.norm_eq_abs] at *
  norm_cast at *

def c₅ : ℝ := ((abs (h7.c₁) + 1) ^ (((↑(h7.h) * (1+4 * h7.m^2)))))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c5nonneg : 0 < h7.c₅ := by
    unfold c₅
    apply pow_pos
    simp only [Int.cast_abs]
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · simp only [abs_nonneg]
    · simp only [zero_lt_one]

/-!so that

$$
|N(\rho)| > c_1^{-h(r+2mq)} > c_5^{-r}.
$$-/

lemma eq5 : h7.c₅ ^ (-(h7.r q hq0 h2mq) : ℝ) < norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
  simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have h1 : 1 ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖ *
      ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ := by
    have := eq5zero h7 q hq0 h2mq
    unfold c1ρ at this
    unfold RingOfIntegers.restrict at this
    simp only [zsmul_eq_mul] at this
    simp only [RingOfIntegers.map_mk, map_mul, norm_mul] at this
    have H := @Algebra.norm_algebraMap ℚ _ h7.K _ _ (h7.cρ q hq0 h2mq)
    simp only [map_intCast] at H
    simp only [norm_pow, ge_iff_le]
    rw [H] at this
    simp only [norm_pow, Int.norm_cast_rat] at this
    exact this
  have h2 : ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹
    ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
    have : 0 < ‖ (h7.cρ q hq0 h2mq)^ Module.finrank ℚ h7.K‖ := by
      rw [norm_pos_iff]
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      intros H
      by_contra H1
      apply h7.cρ_ne_zero q hq0 h2mq
      exact H
    rw [← mul_le_mul_iff_right₀ this]
    · rw [mul_inv_cancel₀]
      · simp_all only [norm_pow]
      · simp only [norm_pow, ne_eq, pow_eq_zero_iff', norm_eq_zero,
          not_and, Decidable.not_not]
        intros H
        rw [H] at this
        simp only [norm_pow, norm_zero] at this
        rw [zero_pow] at this
        · by_contra H1
          simp_all only [norm_pow, lt_self_iff_false]
        · simp_all only [norm_pow]
          have : 0 < Module.finrank ℚ h7.K := by
            exact Module.finrank_pos
          simp_all only [norm_zero, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [pow_zero, one_mul, zero_lt_one, lt_self_iff_false]
  calc _ = _ := ?_
       h7.c₅ ^ ((-h7.r q hq0 h2mq : ℤ)) <
        abs (h7.c₁)^ ((- h7.h : ℤ) * (h7.r q hq0 h2mq + 2 * h7.m * q) ) := ?_
       _ ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹ := ?_
       _ ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := ?_
  · simp only [zpow_neg, zpow_natCast]
  · simp only [zpow_neg, zpow_natCast, neg_mul]
    rw [inv_lt_inv₀]
    · rw [mul_add]
      have : (h7.h : ℤ) * h7.r q hq0 h2mq + h7.h
      * (2 * h7.m * ↑q) = h7.h * h7.r q hq0 h2mq + h7.h * 2 * h7.m * ↑q := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [this]
      have : ((h7.h : ℤ) * h7.r q hq0 h2mq + ↑(h7.h) * 2 * ↑(h7.m) * ↑q)  =
         ((h7.h : ℤ) * (↑(h7.r q hq0 h2mq) + 2 * ↑(h7.m) * ↑q)) :=
         Eq.symm (Mathlib.Tactic.Ring.mul_add rfl rfl this)
      rw [this]
      dsimp [c₅]
      norm_cast
      nth_rw 2 [pow_mul]
      have :  (((abs (h7.c₁) + 1) ^ h7.h) ^ (1 + 4 * h7.m ^ 2)) ^ h7.r q hq0 h2mq=
        ((abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq)) := by
          rw [pow_mul]
          rw [pow_mul]
      rw [this]; clear this
      calc _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 2 * h7.m * q^2)):= ?_
           _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 4 * h7.m ^ 2 * h7.n q)) := ?_
           _ ≤ abs (h7.c₁) ^( h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
           _ < (abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
      · refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn h7 q h2mq]
            simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · trans
              · have : q ≤ q^2 := by
                 refine Nat.le_pow ?_
                 simp only [Nat.ofNat_pos]
                apply this
              · rw [q_sq_eq_two_mn h7 q h2mq]
      · simp only [mul_assoc]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn h7 q h2mq]
            simp only [add_le_add_iff_left]
            have : 2 * (h7.m * (2 * h7.m * h7.n q))=
              4 * h7.m ^ 2 * h7.n q := by
              rw [mul_assoc, mul_assoc]
              ring
            rw [this]
            simp only [mul_assoc,le_refl]
      · rw [mul_add]
        rw [mul_add]
        rw [add_mul]
        simp only [mul_one]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · simp only [add_le_add_iff_left]
          simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · exact n_le_r h7 q hq0 h2mq
      · refine pow_lt_pow_left₀ ?_ ?_ ?_
        · simp only [lt_add_iff_pos_right, zero_lt_one]
        · simp only [abs_nonneg]
        · intros H
          simp only [mul_eq_zero, Nat.add_eq_zero_iff,
            one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, ne_eq, not_false_eq_true, and_true,
             false_or, false_and, or_false] at H
          rcases H with h1 | h2
          · have : 0 ≠ h7.h := by
              symm ;apply Nat.pos_iff_ne_zero.mp
              dsimp [h]
              exact Module.finrank_pos
            apply this
            exact h1.symm
          · apply r_ne_zero h7 q hq0 h2mq
            exact h2
    · unfold c₅
      trans
      · have : (0 : ℝ) < 1 := by simp only [zero_lt_one]
        apply this
      · apply one_lt_pow₀
        · refine one_lt_pow₀ ?_ ?_
          · simp only [Int.cast_abs, lt_add_iff_pos_left, abs_pos, ne_eq, Int.cast_eq_zero]
            rw [← ne_eq]
            exact c₁_ne_zero h7
          · simp only [ne_eq, mul_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, not_false_eq_true, and_true, false_or, false_and, or_false]
            · unfold h
              have : 0 < Module.finrank ℚ h7.K := Module.finrank_pos
              simp_all only [norm_pow, ne_eq]
              apply Aesop.BuiltinRules.not_intro
              intro a
              simp_all only [pow_zero, one_mul, inv_one, lt_self_iff_false]
        · exact r_ne_zero h7 q hq0 h2mq
    · have : 1 ≤ abs (h7.c₁) ^ (↑(h7.h) *
       ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := by
        refine one_le_pow₀ ?_
        have : 1 ≤ h7.c₁ := h7.one_le_c₁
        exact one_le_abs_c₁ h7
      calc (0 : ℝ) < 1 := by simp only [zero_lt_one]
           (1 : ℝ) ≤ abs (h7.c₁) ^ (↑(h7.h) *
           ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := mod_cast this
  · unfold cρ
    simp only [neg_mul, zpow_neg]
    simp only [Int.cast_abs, norm_pow]
    rw [Int.norm_eq_abs]
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
    rw [← abs_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add]
    · rw [← Real.rpow_mul]
      · rw [mul_comm]
        norm_cast
        simp only [Int.cast_pow, Int.cast_abs, abs_pow]
        unfold h
        simp only [le_refl]
      · exact mod_cast (le_trans Int.one_nonneg (h7.one_le_c₁))
    · rw [lt_iff_le_and_ne]
      refine ⟨mod_cast (le_trans Int.one_nonneg (h7.one_le_c₁)), fun H ↦ ?_⟩
      · apply c₁_ne_zero h7
        symm
        exact mod_cast H
  · exact h2

lemma c_coeffspow_r :
  ((h7.c₁) ^ (h7.r q hq0 h2mq) * (h7.c₁) ^ (h7.m * q) * (h7.c₁) ^ (h7.m * q)) =
  ((h7.c₁) ^ ((h7.r q hq0 h2mq)) *
  (h7.c₁) ^ (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) *
  (h7.c₁) ^ (h7.m * q - ((b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))) •
  (h7.c₁) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
  (h7.c₁) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) := by
    rw [← one_mul (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq : ℕ) + 1)))]
    have triple_comm_int (a b c : ℤ) (x y z : ℤ) :
      ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
     simp only [zsmul_eq_mul, Int.cast_mul]; ring
    simp only [mul_assoc]
    rw [ smul_mul_assoc
          (h7.c₁ ^ h7.r q hq0 h2mq *
            (h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
              h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))
          (1 * h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
          (h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    rw [Int.mul_assoc 1 (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
          (h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    simp only [← mul_assoc]
    rw [triple_comm_int]
    congr
    · simp only [Int.zsmul_eq_mul, mul_one]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      + (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (zero_le _) (zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        + (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (zero_le _) (zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]

end Setup

end
