/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainOrder
public import Mathlib.Analysis.Analytic.Order

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

lemma iteratedkDeriv_R_eq_zero (k : Fin (h7.n q)) (l' : Fin h7.m) :
    deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
  have h1 := h7.coeffs_mul_deriv_eq_zero q hq0 (finProdFinEquiv ⟨l', k⟩) h2mq
  simp only [Setup.k, Setup.l, Equiv.toFun_as_coe, Equiv.symm_apply_apply,
    Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg, zpow_natCast,
    Nat.cast_add, Nat.cast_one, ← mul_assoc] at h1
  refine (mul_eq_zero.mp h1).resolve_left (fun h_zero ↦ ?_)
  have h_log : Complex.log h7.α ≠ 0 := fun h ↦
    h7.htriv.2 (by simpa [exp_log h7.htriv.1] using congrArg exp h)
  simp only [mul_eq_zero, inv_eq_zero, pow_eq_zero_iff'] at h_zero
  revert h_zero
  simp [h7.c₁_ne_zero, h_log]

open AnalyticOnNhd

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

lemma exists_analyticOrderAt_R_eq_some (z : ℂ) :
    ∃ r, (analyticOrderAt (h7.R q hq0 h2mq) z) = some r := by
  have : (analyticOrderAt (h7.R q hq0 h2mq) z) ≠ ⊤ :=
    h7.order_neq_top_min_one q hq0 h2mq z
  revert this
  cases (analyticOrderAt (h7.R q hq0 h2mq) z) with
  | top => grind
  | coe => aesop

def R_order (z : ℂ) : ℕ := (exists_analyticOrderAt_R_eq_some h7 q hq0 h2mq z).choose

def R_order_prop {z : ℂ} := (exists_analyticOrderAt_R_eq_some h7 q hq0 h2mq z).choose_spec

lemma R_order_eq (z) : (analyticOrderAt (h7.R q hq0 h2mq) z) = h7.R_order q hq0 h2mq z :=
  (exists_analyticOrderAt_R_eq_some h7 q hq0 h2mq z).choose_spec

lemma r_exists : ∃ r, r' h7 q hq0 h2mq = some r := by
  have H := order_neq_top_min_one h7 q hq0 h2mq (l₀' h7 q hq0 h2mq + 1)
  have : r' h7 q hq0 h2mq ≠ ⊤ := by rw [(r'_spec h7 q hq0 h2mq).1] at H; exact H
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
  apply h7.r'_spec q hq0 h2mq

lemma r_div_q_geq_0 : 0 ≤ (h7.r q hq0 h2mq) / q := by simp_all only [zero_le]


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

lemma systemCoeffs_map_eq_exp_mul_r :
  exp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) *
  h7.ρ q t ^ (h7.r q hq0 h2mq : ℕ) *
  Complex.log h7.α ^ (-(h7.r q hq0 h2mq) : ℤ) = h7.σ (h7.systemCoeffs_r q hq0 t h2mq) := by
    nth_rw 2 [ρ]
    rw [mul_pow, mul_assoc, mul_assoc]
    have hlog : Complex.log h7.α ≠ 0 := by
      intro h
      exact h7.htriv.2 (by simpa [Complex.exp_log h7.htriv.1] using congrArg Complex.exp h)
    have : Complex.log h7.α ^ (h7.r q hq0 h2mq : ℕ) *
      Complex.log h7.α ^ (-h7.r q hq0 h2mq : ℤ) = 1 := by
      simp [zpow_neg, zpow_natCast, hlog]
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
          aesop
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
    · have hmul :
          Complex.log h7.α *
            (↑(a q t) * (h7.l₀' q hq0 h2mq + 1) +
              ((b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β) =
            (↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1) := by
        simp [nsmul_eq_mul]
        ring
      simp [hmul]
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
  have := systemCoeffs_map_eq_exp_mul_r h7 q hq0 t h2mq
  rw [← this]

def rho := ∑ t : Fin (q * q), (h7.η q hq0 h2mq t) * (h7.systemCoeffs_r q hq0 t h2mq)

def rho_eq_ρᵣ : h7.σ (rho h7 q hq0 h2mq) = ρᵣ h7 q hq0 h2mq := by
  unfold rho ρᵣ
  rw [systemCoeffs_deriv_r]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]

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
      · refine IsIntegral.mul ?_ ?_
        · have hbase : IsIntegral ℤ (↑h7.c₁ * (↑(a q x) + b q x • h7.β')) := by
            rw [mul_add]
            refine (IsIntegral.add (R := ℤ) (A := h7.K) ?_ ?_)
            · simpa [mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (a q x)) (IsIntegral.Cast h7.K h7.c₁))
            · simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (b q x)) h7.isIntegral_c₁β)
          simpa [Nat.mul_one] using
            (h7.isIntegral_c₁_pow_smul_pow
              (u := (↑(a q x) + b q x • h7.β'))
              (n := h7.r q hq0 h2mq) (k := 1) (a := h7.r q hq0 h2mq) (l := 1)
              (by simp) hbase)
        · refine h7.isIntegral_c₁_pow_smul_pow
            (u := h7.α') (n := h7.m) (k := q) (a := a q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
          · rw [mul_comm]
            exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
              (finProdFinEquiv.symm.toFun x).1.isLt
          · simpa [zsmul_eq_mul] using h7.isIntegral_c₁α
      · refine h7.isIntegral_c₁_pow_smul_pow
          (u := h7.γ') (n := h7.m) (k := q) (a := b q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
        · rw [mul_comm]
          exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
            (finProdFinEquiv.symm.toFun x).2.isLt
        · simpa [zsmul_eq_mul] using h7.isIntegral_c₁γ
  · rw [Finset.smul_sum]
    apply IsIntegral.sum
    intro x hx
    have hmul :
        IsIntegral ℤ
          (h7.c₁ ^ (h7.r q hq0 h2mq) • (↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
            h7.c₁ ^ (h7.m * q) • h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
            h7.c₁ ^ (h7.m * q) • h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1))) := by
      refine IsIntegral.mul ?_ ?_
      · refine IsIntegral.mul ?_ ?_
        · have hbase : IsIntegral ℤ (↑h7.c₁ * (↑(a q x) + b q x • h7.β')) := by
            rw [mul_add]
            refine IsIntegral.add (R := ℤ) (A := h7.K) ?_ ?_
            · simpa [mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (a q x)) (IsIntegral.Cast h7.K h7.c₁))
            · simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
                (IsIntegral.mul (IsIntegral.Nat h7.K (b q x)) h7.isIntegral_c₁β)
          simpa [Nat.mul_one] using
            (h7.isIntegral_c₁_pow_smul_pow
              (u := (↑(a q x) + b q x • h7.β'))
              (n := h7.r q hq0 h2mq) (k := 1) (a := h7.r q hq0 h2mq) (l := 1)
              (by simp) hbase)
        · refine h7.isIntegral_c₁_pow_smul_pow
            (u := h7.α') (n := h7.m) (k := q) (a := a q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
          · rw [mul_comm]
            exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
              (finProdFinEquiv.symm.toFun x).1.isLt
          · simpa [zsmul_eq_mul] using h7.isIntegral_c₁α
      · refine h7.isIntegral_c₁_pow_smul_pow
          (u := h7.γ') (n := h7.m) (k := q) (a := b q x) (l := h7.l₀' q hq0 h2mq + 1) ?_ ?_
        · rw [mul_comm]
          exact Nat.mul_le_mul (h7.l₀' q hq0 h2mq).isLt
            (finProdFinEquiv.symm.toFun x).2.isLt
        · simpa [zsmul_eq_mul] using h7.isIntegral_c₁γ
    have hη : IsIntegral ℤ (↑((h7.η q hq0 h2mq) x) : h7.K) :=
      RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    have hnegScaled :
        IsIntegral ℤ
          ((↑(-(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) : ℤ) : h7.K) *
            ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
              h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
              h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) := by
      have hscaled :
          IsIntegral ℤ
            ((↑(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q) : ℤ) : h7.K) *
              ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
                h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
                h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) := by
        convert hmul using 1
        grind
      convert (IsIntegral.neg hscaled) using 1
      grind
    have habs :
        |h7.c₁ ^ (h7.r q hq0 h2mq) * (h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q))| =
          -(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) := by
      simpa [mul_assoc] using H2
    rw [habs, zsmul_eq_mul]
    have hmulInt :
        IsIntegral ℤ
          (((↑(-(h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) : ℤ) : h7.K) *
              ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
                h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
                h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) *
            (↑((h7.η q hq0 h2mq) x) : h7.K)) := by
      exact IsIntegral.mul hnegScaled hη
    convert hmulInt using 1
    ac_rfl

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

lemma cρ_le_abs_cρ :
    (h7.cρ q hq0 h2mq) ≤ abs (h7.cρ q hq0 h2mq):= le_abs_self _

lemma abs_cρ_le_norm_cρ :
    abs (h7.cρ q hq0 h2mq) ≤ norm (h7.cρ q hq0 h2mq) := by
  simp only [Int.cast_abs]
  rfl

lemma norm_cρ_le_house_cρ : norm (h7.cρ q hq0 h2mq) ≤
  house (h7.cρ q hq0 h2mq : h7.K) := by
  rw [house_intCast]
  simp only [Int.cast_abs]
  exact Preorder.le_refl ‖h7.cρ q hq0 h2mq‖

lemma norm_cρ_pos : 0 < ‖h7.cρ q hq0 h2mq‖ := by
  rw [norm_pos_iff]
  have := h7.cρ_ne_zero q hq0 h2mq
  unfold cρ at this
  exact this

lemma one_le_norm_cρ_pow : 1 ≤ ‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K := by
  rw [one_le_pow_iff_of_nonneg]
  · simpa using h7.one_le_norm_c1rho q hq0 h2mq
  · exact norm_nonneg _
  · exact Nat.ne_of_gt Module.finrank_pos

end Setup

end
