/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainOrder
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.AnalyticPart

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

lemma R_analyt_at_point (point : ℂ) : AnalyticAt ℂ (h7.R q hq0 h2mq) point := by
  fun_prop

lemma anever : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
  fun_prop

lemma order_neq_top : ∀ (l' : Fin (h7.m)), analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply h7.R_nonzero q hq0 h2mq (by aesop)
  exact (fun z ↦ h7.anever q hq0 h2mq z)

lemma order_neq_top_min_one : ∀ z : ℂ, analyticOrderAt (h7.R q hq0 h2mq) z ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply h7.R_nonzero
    · rw [funext_iff]
      intros z
      rw [funext_iff] at H
      apply H z
  intros z
  exact h7.anever q hq0 h2mq z

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

lemma exists_min_order_at :
  let s : Finset (Fin (h7.m)) := Finset.univ
  ∃ l₀' ∈ s, (∃ y, (analyticOrderAt (h7.R q hq0 h2mq) (l₀' + 1)) = y ∧
   (∀ (l' : Fin (h7.m)), l' ∈ s → y ≤ (analyticOrderAt (h7.R q hq0 h2mq) (l' + 1)))) := by
  intros s
  have Hs : s.Nonempty := by
     refine univ_nonempty_iff.mpr ?_
     refine Fin.pos_iff_nonempty.mp ?_
     exact (Nat.zero_lt_succ (2 * h7.h + 1))
  let f : (Fin (h7.m)) → ℕ∞ := fun x => (analyticOrderAt (h7.R q hq0 h2mq) (x + 1))
  have  exists_mem_finset_min' {γ : Type _} {β : Type _} [LinearOrder γ]
    (s : Finset β) (f : β → γ) (Hs : s.Nonempty) :
    ∃ x ∈ s, ∃ y, y = f x ∧ ∀ x' ∈ s, y ≤ f x' := by
      obtain ⟨x, hxs, hx⟩ := s.exists_min_image f Hs
      exact ⟨x, hxs, f x, rfl, hx⟩
  have := exists_mem_finset_min' s f Hs
  obtain ⟨x, hx, ⟨r, h1, h2⟩⟩ := this
  use x
  refine ⟨hx, ?_⟩
  · constructor; refine ⟨id (Eq.symm h1), fun x hx ↦ h2 x hx⟩

abbrev l₀' : Fin (h7.m) := (exists_min_order_at h7 q hq0 h2mq).choose

abbrev l₀_prop :=
  (exists_min_order_at h7 q hq0 h2mq).choose_spec.2

abbrev r' := (l₀_prop h7 q hq0 h2mq).choose

abbrev r'_prop :
  let s : Finset (Fin (h7.m)) := Finset.univ
  analyticOrderAt (h7.R q hq0 h2mq) ↑↑(h7.l₀' q hq0 h2mq + 1 : ℂ) =
    h7.r' q hq0 h2mq ∧
    ∀ l' ∈ s, h7.r' q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' +1) := by
  exact (h7.l₀_prop q hq0 h2mq).choose_spec

lemma r_exists :
  ∃ r, r' h7 q hq0 h2mq = some r := by
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
  analyticOrderAt (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
   h7.r q hq0 h2mq ∧
  ∀ l' ∈ s, h7.r q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' + 1) := by
  intros s
  rw [← h7.r_spec q hq0 h2mq]
  apply h7.r'_prop q hq0 h2mq

lemma r_div_q_geq_0 : 0 ≤ (h7.r q hq0 h2mq) / q := by simp_all only [zero_le]

lemma exists_nonzero_iteratedFDeriv : deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) ≠ 0 := by
  have Hrprop := (h7.r_prop q hq0 h2mq).1
  obtain ⟨l₀, y, r, h1, h2⟩ :=
    (h7.exists_min_order_at q hq0 h2mq)
  have hA1 := h7.R_analyt_at_point q hq0 h2mq (h7.l₀' q hq0 h2mq + 1)
  grind [analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero hA1]

lemma order_geq_n_foo (l' : Fin (h7.m)) :
  (∀ k', k' < h7.n q → deriv^[k'] (h7.R q hq0 h2mq) (l' + 1) = 0)
   → h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros H
  apply le_analyticOrderAt_iff_iteratedDeriv_eq_zero
  · exact h7.anever q hq0 h2mq (l' + 1)
  · apply order_neq_top h7 q hq0 h2mq l'
  exact H

lemma order_geq_n : ∀ l' : Fin (h7.m),
    h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros l'
  apply order_geq_n_foo
  intros k hk
  have H := h7.iteratedDeriv_vanishes q hq0 h2mq ⟨k,hk⟩ l'
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

lemma r_qt_0 : 0 < h7.r q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (h7.r_ne_zero q hq0 h2mq)

lemma one_le_r : 1 ≤  h7.r q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (h7.r_ne_zero q hq0 h2mq)

def cρ : ℤ := abs (h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁^(2*h7.m * q))

abbrev sys_coe_r : h7.K := (a q t + b q t • h7.β')^(h7.r q hq0 h2mq) *
 h7.α' ^(a q t * (h7.l₀' q hq0 h2mq + 1)) * h7.γ' ^(b q t * (h7.l₀' q hq0 h2mq + 1))

lemma sys_coe_ne_zero_r : h7.sys_coe_r q hq0 t h2mq ≠ 0 := by
  unfold sys_coe_r
  intros H
  simp only [mul_eq_zero, pow_eq_zero_iff'] at H
  cases H with
  | inl H1 =>
    cases H1 with
    | inl H1 =>
      rcases H1 with ⟨h1, h2⟩
      apply (h7.β'_neq_zero q t (h7.r q hq0 h2mq))
      rw [h1]
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact h2
    | inr H2 => exact h7.alpha'_beta'_gamma'_ne_zero.1 H2.1
  | inr H2 =>
    exfalso
    exact h7.alpha'_beta'_gamma'_ne_zero.2.2 H2.1

def ρᵣ : ℂ := (Complex.log h7.α)^(-(h7.r q hq0 h2mq) : ℤ) *
 deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1)

lemma sys_coe_bar_r :
  exp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) *
  h7.ρ q t ^ (h7.r q hq0 h2mq : ℕ) *
  Complex.log h7.α ^ (-(h7.r q hq0 h2mq) : ℤ) = h7.σ (h7.sys_coe_r q hq0 t h2mq) := by
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
    unfold sys_coe_r
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
  rw [iteratedDeriv_of_R]

lemma sys_coe_foo_r :
 (Complex.log h7.α)^(-h7.r q hq0 h2mq : ℤ) * deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
 ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.sys_coe_r q hq0 t h2mq) := by
  rw [h7.deriv_R_k_eval_at_l0' q hq0 h2mq, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  unfold η
  simp only [mul_eq_mul_left_iff, map_eq_zero,
    FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := sys_coe_bar_r h7 q hq0 t h2mq
  rw [← this]


def rho := ∑ t : Fin (q * q), (h7.η q hq0 h2mq t) * (h7.sys_coe_r q hq0 t h2mq)

def rho_eq_ρᵣ : h7.σ (rho h7 q hq0 h2mq) = ρᵣ h7 q hq0 h2mq := by
  unfold rho ρᵣ
  rw [sys_coe_foo_r]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]

lemma ρᵣ_nonzero : ρᵣ h7 q hq0 h2mq ≠ 0 := by
  unfold ρᵣ
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  refine ⟨fun hlog => ?_, h7.exists_nonzero_iteratedFDeriv q hq0 h2mq⟩
  · by_contra H
    have : Complex.log h7.α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2
    apply this; exact hlog

lemma rho_nonzero : rho h7 q hq0 h2mq ≠ 0 := by
  intros H
  apply_fun h7.σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply h7.ρᵣ_nonzero
  exact H

lemma cρ_ne_zero : h7.cρ q hq0 h2mq ≠ 0 := by
  apply abs_ne_zero.mpr <| mul_ne_zero _ _
  all_goals apply pow_ne_zero _ (h7.c₁_ne_zero)

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c₁bρ (a b n : ℕ) : 1 ≤ n → h7.k q u ≤ n - 1 → 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) →
  IsIntegral ℤ (h7.c₁^(n - 1) • (a + b • h7.β') ^ (h7.k q u)) := by
  intros hn hkn ha hb
  have : h7.c₁^(n - 1) = h7.c₁ ^ (n - 1 - (h7.k q u)) * h7.c₁^(h7.k q u) := by
    simp_all only [← pow_add, Nat.sub_add_cancel]
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow
    · apply IsIntegral.Cast
  rw [← mul_pow]
  apply IsIntegral.pow
  rw [mul_add]
  apply IsIntegral.add
  · apply IsIntegral.mul <| IsIntegral.Cast _ _
    · apply IsIntegral.Nat
  rw [mul_comm, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.Nat _ _
  rw [mul_comm, ← zsmul_eq_mul]
  exact h7.isIntegral_c₁β

lemma ρ_is_int :
  IsIntegral ℤ (h7.cρ q hq0 h2mq • rho h7 q hq0 h2mq) := by
  unfold rho cρ sys_coe_r
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
        · apply h7.c₁ac
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
        · apply h7.c₁ac
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

lemma eq5 : h7.c₅ ^ (-(h7.r q hq0 h2mq) : ℝ)
  < norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
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
          · rw [q_eq_2sqrtmn h7 q h2mq]
            simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · trans
              · have : q ≤ q^2 := by
                 refine Nat.le_pow ?_
                 simp only [Nat.ofNat_pos]
                apply this
              · rw [q_eq_2sqrtmn h7 q h2mq]
      · simp only [mul_assoc]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_eq_2sqrtmn h7 q h2mq]
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
          cases' H with h1 h2
          · have : 0 ≠ h7.h := by
              symm ;apply Nat.pos_iff_ne_zero.mp
              dsimp [h]
              exact Module.finrank_pos
            apply this
            exact h1.symm
          · apply r_ne_zero h7 q hq0 h2mq
            exact h2
    ·
      unfold c₅
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

lemma crho_abs_eq : |h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q)| =
  h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q) := by
    rw [abs_eq_self]
    apply mul_nonneg (pow_nonneg (le_trans Int.one_nonneg h7.one_le_c₁) _)
    · apply pow_nonneg (le_trans Int.one_nonneg h7.one_le_c₁)

def c₆ : ℝ := (|↑h7.c₁| * (1 + house h7.β'))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c₆_nonneg : 0 ≤ h7.c₆ := by
  unfold c₆ house; positivity

omit [DecidableEq (h7.K →+* ℂ)] in
lemma one_le_c₆ : 1 ≤ h7.c₆ := by
  unfold c₆
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · norm_cast; exact one_le_abs_c₁ h7
  · simp only [le_add_iff_nonneg_right]
    exact house_nonneg h7.β'

def c₇ : ℝ := ((((|↑h7.c₁| * |↑h7.c₁| *
  (|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))))) ^ h7.m))

lemma one_le_c₇ : 1 ≤ h7.c₇ := by
  unfold c₇
  simp only [abs_mul_abs_self]
  have hc: 0 ≤ h7.c₁ := by exact le_trans Int.one_nonneg h7.one_le_c₁
  have  house_num_mul_int (α : h7.K) (c' : ℤ) (hc : 0 ≤ c') :
    house ((c' : h7.K) * α) = |(c' : ℝ)| * house (α) := by
        lift c' to ℕ using hc
        simpa using house_nat_mul α c'
  have := house_num_mul_int (c':=h7.c₁) (α := h7.γ') hc
  rw [← this]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [mul_assoc (↑h7.c₁ * (h7.c₁:ℝ)) |↑h7.c₁| (house h7.α')]
  have := house_num_mul_int (c':=h7.c₁) (α := h7.α') hc
  rw [← this]
  calc _ ≤ (↑h7.c₁ * ↑h7.c₁ * house (↑h7.c₁ * h7.α') * house (↑h7.c₁ * h7.γ')) := ?_
       _ ≤ (↑h7.c₁ * ↑h7.c₁ * house (↑h7.c₁ * h7.α') * house (↑h7.c₁ * h7.γ')) ^ h7.m := ?_
  · refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · refine one_le_mul_of_one_le_of_one_le ?_ ?_
        · norm_cast; exact one_le_c₁ h7
        · norm_cast; exact one_le_c₁ h7
      · rw [← smul_eq_mul]
        refine one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁α) (mod_cast h7.c₁α_ne_zero)
    · rw [← smul_eq_mul]
      refine one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁γ) (mod_cast h7.c₁c_ne_zero)
  · nth_rw 1 [← pow_one (a :=↑h7.c₁ * ↑h7.c₁ *
      house (↑h7.c₁ * h7.α') * house (↑h7.c₁ * h7.γ'))]
    refine pow_le_pow_right₀ ?_ ?_
    · refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · refine one_le_mul_of_one_le_of_one_le ?_ ?_
        · refine one_le_mul_of_one_le_of_one_le ?_ ?_
          · norm_cast; exact one_le_c₁ h7
          · norm_cast; exact one_le_c₁ h7
        · rw [← smul_eq_mul]
          refine one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁α) (mod_cast h7.c₁α_ne_zero)
      · rw [← smul_eq_mul]
        refine one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁γ) (mod_cast h7.c₁c_ne_zero)
    · unfold m
      exact Nat.le_add_left 1 (2 * h7.h + 1)

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
        apply mul_le_mul (a_le_q q t) ?_ (zero_le _) (zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        + (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (b_le_q q t) ?_ (zero_le _) (zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]


lemma eq6a : house (rho h7 q hq0 h2mq) ≤
  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := by
  calc
       _ ≤ norm (h7.cρ q hq0 h2mq : ℝ) * house (rho h7 q hq0 h2mq) := ?_

       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ))  *
          house (∑ t, ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
        ((h7.sys_coe_r q hq0 t h2mq)))) := ?_

       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ)) *
         ∑ t, house ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
       ((h7.sys_coe_r q hq0 t h2mq))) := ?_

       _ = (∑ t, house ((h7.cρ q hq0 h2mq) *
         (algebraMap (𝓞 h7.K) h7.K ((h7.η q hq0 h2mq) t) *
          h7.sys_coe_r q hq0 t h2mq))) := ?_

       _ = ∑ t, house ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq t) *
        (↑h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
          (↑h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
            (h7.c₁ ^ h7.r q hq0 h2mq • (↑(a q t) + b q t • h7.β') ^ h7.r q hq0 h2mq *
              (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.α' ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
                h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.γ' ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))))) := ?_

       _ ≤ ∑ t, house ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq t)) *
        (house (((h7.c₁ : h7.K) ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
          (house (((h7.c₁ : h7.K) ^
              (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
            (house (((h7.c₁ : h7.K) ^ h7.r q hq0 h2mq •
              (↑(a q t) + b q t • h7.β') ^ h7.r q hq0 h2mq)) *
              (house (((h7.c₁ : h7.K) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.α' ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
                (house ((h7.c₁ : h7.K) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.γ' ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
                  ))))) := ?_

       _ ≤ (∑ t, h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (↑|h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1))| *
        (↑|h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1))| *
          (((|h7.c₁| * (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.r q hq0 h2mq)) *
             house ((h7.c₁ • h7.α')) ^ (h7.m * q) *
             house ((h7.c₁ • h7.γ')) ^ (h7.m * q))))) := ?_

       _ ≤ ∑ (t : Fin (q * q)), h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
          (↑|h7.c₁| ^ (h7.m * q) *
          (↑|h7.c₁| ^ (h7.m * q) *
          ((|h7.c₁|^ (h7.r q hq0 h2mq) *
            (|(q : ℤ)|^ (h7.r q hq0 h2mq) * (1 + house (h7.β')) ^ (h7.r q hq0 h2mq)) *
             ((|h7.c₁|^ (h7.m * q) * house (h7.α') ^ (h7.m * q)) *
             (|h7.c₁|^ (h7.m * q)  * house h7.γ' ^ (h7.m * q))))))) := ?_

       _ ≤  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := ?_

  · rw [← one_mul (house (h7.rho q hq0 h2mq))]
    apply mul_le_mul
    · exact h7.one_le_norm_c1rho q hq0 h2mq
    · simp only [one_mul, le_refl]
    · exact house_nonneg (h7.rho q hq0 h2mq)
    · simp only [norm_nonneg]
  · unfold rho
    simp only [le_refl]
  · apply mul_le_mul (le_refl _)
    · exact
      house_sum_le_sum_house Finset.univ fun i ↦
        (algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq i)
        * h7.sys_coe_r q hq0 i h2mq
    · exact
      house_nonneg (∑ t, (algebraMap (𝓞 h7.K) h7.K)
        (h7.η q hq0 h2mq t) * h7.sys_coe_r q hq0 t h2mq)
    · exact norm_nonneg (h7.cρ q hq0 h2mq)
  · rw [mul_sum]
    apply Finset.sum_congr rfl
    intros i hi
    have  house_num_mul_int (α : h7.K) (c' : ℤ) (hc : 0 ≤ c') :
    house ((c' : h7.K) * α) = |(c' : ℝ)| * house (α) := by
        lift c' to ℕ using hc
        simpa using house_nat_mul α c'
    rw [house_num_mul_int
    (α := ((algebraMap (𝓞 h7.K) h7.K)
    (h7.η q hq0 h2mq i) * h7.sys_coe_r q hq0 i h2mq))]
    · simp only [Real.norm_eq_abs]
    · exact zero_le_c1rho h7 q hq0 h2mq
  · apply Finset.sum_congr rfl
    intros t ht
    rw [Algebra.left_comm (↑(h7.cρ q hq0 h2mq))
      (h7.η q hq0 h2mq t) (h7.sys_coe_r q hq0 t h2mq)]
    simp only [← zsmul_eq_mul]
    unfold sys_coe_r
    unfold cρ
    rw [crho_abs_eq]
    have : h7.c₁ ^ (2 * h7.m * q) = h7.c₁ ^ (h7.m * q)
     * h7.c₁ ^ (h7.m * q) := by
       rw [← pow_add]; ring
    rw [this]; clear this
    have := h7.c_coeffspow_r q hq0 t h2mq
    simp only [mul_assoc] at this
    rw [this]; clear this
    rw [Int.mul_comm (h7.c₁ ^ h7.r q hq0 h2mq)
     (h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
    h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    simp only [mul_assoc]
    simp only [nsmul_eq_mul, zsmul_eq_mul,
     Int.cast_mul, Int.cast_pow]
    simp only [mul_assoc]
    simp only [Int.cast_eq]
    ring_nf
  · apply Finset.sum_le_sum
    intros t ht
    · trans
      · apply house_mul_le
      · refine mul_le_mul_of_nonneg (le_refl _) ?_ ?_ ?_
        · trans
          apply house_mul_le
          · refine mul_le_mul_of_nonneg (le_refl _) ?_ ?_ ?_
            · trans
              apply house_mul_le
              refine mul_le_mul_of_nonneg (le_refl _) ?_ ?_ ?_
              · trans
                apply house_mul_le
                refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                · simp only [nsmul_eq_mul, zsmul_eq_mul,
                    Int.cast_pow, smul_eq_mul, le_refl]
                · trans
                  apply house_mul_le
                  unfold house
                  refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                  · simp
                  · simp
                  · positivity
                  · positivity
                · apply house_nonneg
                · dsimp [house]; positivity
              · apply house_nonneg
              · dsimp [house]; positivity
            · apply house_nonneg
            · dsimp [house]; positivity
        · apply house_nonneg
        · dsimp [house]; positivity
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · apply h7.fromlemma82_bound q hq0 t h2mq
    · simp only [mul_assoc]
      apply mul_le_mul
      · norm_cast
        rw [house_intCast]
      · apply mul_le_mul
        · norm_cast
          rw [house_intCast]
        · apply mul_le_mul
          · simp only [nsmul_eq_mul, smul_eq_mul]
            rw [← mul_pow]
            rw [mul_add]
            calc _ ≤  house ((↑h7.c₁ * ↑(a q t) + ↑h7.c₁ *
                  (↑(b q t) * h7.β'))) ^ h7.r q hq0 h2mq :=?_
                 _ ≤  (↑|h7.c₁| * (↑|↑q| * (1 + house h7.β'))) ^ h7.r q hq0 h2mq := ?_
            · apply house_pow_le _ _

            · rw [← mul_add]
              rw [pow_le_pow_iff_left₀]
              · have := house_add_mul_le h7 q t
                simp only [mul_assoc] at *
                norm_cast at *
                simp only [nsmul_eq_mul, zsmul_eq_mul] at this
                exact this
              · apply house_nonneg
              · unfold house
                positivity
              · exact r_ne_zero h7 q hq0 h2mq
            · simp only [Int.cast_abs, Nat.abs_cast, Int.cast_natCast, le_refl]
          · apply mul_le_mul
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              · apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁α
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁α_ne_zero
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (a_le_q q t) ?_ (zero_le _) (zero_le _)
                · exact (h7.l₀' q hq0 h2mq).isLt
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁γ
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁c_ne_zero
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (b_le_q q t) ?_ (zero_le _) (zero_le _)
                · exact (h7.l₀' q hq0 h2mq).isLt
            · apply house_nonneg
            · unfold house; positivity
          · unfold house; positivity
          · unfold house; positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact zero_le_c₄ h7
      · positivity
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply mul_le_mul
      · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
        refine pow_le_pow_right₀ ?_ ?_
        · norm_cast; exact one_le_abs_c₁ h7
        · exact Nat.sub_le (h7.m * q) (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      · apply mul_le_mul
        · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
          refine pow_le_pow_right₀ ?_ ?_
          · norm_cast; exact one_le_abs_c₁ h7
          · exact Nat.sub_le (h7.m * q) (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        · nth_rw 1 [mul_assoc]
          apply mul_le_mul
          · rw [← mul_pow]; rw [← mul_pow]
          · apply mul_le_mul
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (h7.m * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (h7.m * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · unfold house; positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact zero_le_c₄ h7
      · positivity
  · simp only [ sum_const, card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    apply mul_le_mul
    · simp only [Nat.cast_mul, le_refl]
    · nth_rw 4 [mul_assoc]
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · simp only [← mul_assoc]
        rw [← mul_pow]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        rw [← mul_pow]
        simp only [Int.cast_abs,
        Nat.abs_cast, Int.cast_natCast, zpow_natCast]
        rw [mul_comm ((1 + house h7.β') ^ h7.r q hq0 h2mq)
          ((|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))) ^ (h7.m * q))]
        nth_rw 3 [← mul_assoc]
        rw [mul_comm ((q:ℝ) ^ h7.r q hq0 h2mq)
         ((|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))) ^ (h7.m * q))]
        nth_rw 2 [← mul_assoc]
        rw [mul_comm  (|(h7.c₁ : ℝ)| ^ h7.r q hq0 h2mq)
          ((|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| *
           house h7.γ'))) ^ (h7.m * q) * (q : ℝ) ^ h7.r q hq0 h2mq)]
        nth_rw 1 [← mul_assoc]
        rw [mul_comm  ((h7.c₆ * ↑q) ^ h7.r q hq0 h2mq) (h7.c₇ ^ q)]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        nth_rw 1 [← mul_assoc]
        rw [← mul_pow]
        rw [pow_mul]
        rw [← mul_comm  (q : ℝ)  h7.c₆]
        unfold c₇ c₆
        simp only [mul_assoc]
        rfl
      · unfold house; positivity
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact zero_le_c₄ h7
        · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact zero_le_c₄ h7
        · positivity
      · unfold house; positivity
    · positivity

theorem bound_n_le_r' :
   ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
     ((h7.r q hq0 h2mq : ℝ)^((1/2) * ((h7.r q hq0 h2mq : ℝ) + 1))) := by
      calc _ ≤ ((h7.r q hq0 h2mq : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) := ?_
           _ ≤ ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))) := ?_
      · refine Real.rpow_le_rpow ?_ ?_ ?_
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_le]; exact n_le_r h7 q hq0 h2mq
        · refine div_nonneg ?_ ?_
          · norm_cast
            exact Nat.le_add_left 0 (h7.n q + 1)
          · simp only [Nat.ofNat_nonneg]
      · apply Real.rpow_le_rpow_of_exponent_le_or_ge
        left
        · simp only [Nat.one_le_cast, one_div]
          refine ⟨r_qt_0 h7 q hq0 h2mq, ?_⟩
          · ring_nf
            simp only [one_div, add_le_add_iff_left,
             inv_pos, Nat.ofNat_pos, mul_le_mul_iff_left₀, Nat.cast_le]
            exact n_le_r h7 q hq0 h2mq

lemma bound_n_le_r :
  (h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
  ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)) *
    ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))))) := by
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      refine pow_le_pow_right₀ (one_le_c₄ h7) (n_le_r h7 q hq0 h2mq)
    · exact bound_n_le_r' h7 q hq0 h2mq
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
    · apply Real.rpow_nonneg
      exact zero_le_c₄ h7

lemma q_le_2sqrtmr : q^2 ≤ 2*h7.m*h7.r q hq0 h2mq := by
  trans
  apply h7.sq_le_two_mn q h2mq
  refine Nat.mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq)

lemma sqt_etc : Real.sqrt (2*h7.m*(h7.r q hq0 h2mq)) =
  Real.sqrt (2*h7.m) * (h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ) := by
    rw [Real.sqrt_mul]
    · congr
      exact Real.sqrt_eq_rpow ↑(h7.r q hq0 h2mq)
    · positivity

def c₈ : ℝ := (h7.c₆ * √(2 * ↑h7.m) * h7.c₇ ^ (2 * h7.m) * h7.c₄ * (2 * ↑h7.m))

lemma c7_nonneg : 0 ≤ h7.c₇ := by
  unfold c₇ house
  positivity

lemma c8_nonneg : 0 ≤ h7.c₈ := by
  unfold c₈
  apply mul_nonneg ?_ (by positivity)
  · apply mul_nonneg ?_ (zero_le_c₄ h7)
    · apply mul_nonneg (mul_nonneg (c₆_nonneg h7) (by simp)) (pow_nonneg (c7_nonneg h7) _)

lemma c8_geq_one : 1 ≤ h7.c₈ := by
  unfold c₈
  have : 1 ≤ h7.c₆ := h7.one_le_c₆
  have : 1 ≤ h7.c₇ := h7.one_le_c₇
  have := h7.one_le_c₄
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · apply one_le_mul_of_one_le_of_one_le
        · (expose_names; exact this_1)
        · rw [Real.one_le_sqrt]
          apply one_le_mul_of_one_le_of_one_le (by grind) ?_
          · simp only [Nat.one_le_cast]
            exact Nat.le_of_ble_eq_true rfl
      · (expose_names; exact one_le_pow₀ this_2)
    · exact this
  · apply one_le_mul_of_one_le_of_one_le (by grind) ?_
    · simp only [Nat.one_le_cast]
      exact Nat.le_of_ble_eq_true rfl

lemma zero_lt_r : 0 < h7.r q hq0 h2mq :=
  r_qt_0 h7 q hq0 h2mq

theorem q_sq2_neq_1 (m q : ℕ) (hq0 : 0 < q)
    (h2mq : 2 * m ∣ q ^ 2) : q ^ 2 ≠ 1 := by
  intro hq2eq1
  have hdiv1 : 2 * m ∣ 1 := by
    exact (Nat.ModEq.dvd_iff
     (congrFun (congrArg HMod.hMod hq2eq1) (q ^ 2)) h2mq).mp h2mq
  cases m with
  | zero => simp [*] at hdiv1
  | succ m' =>
    have h_two_eq_one : 2 * (m'.succ) = 1 := Nat.eq_one_of_dvd_one hdiv1
    have h_ge_two : 2 * (m'.succ) ≥ 2 := by
      calc
        2 * (m'.succ) = 2 + 2 * m' := by
          simp only [Nat.succ_eq_add_one]
          ring_nf
        _ ≥ 2 := Nat.le_add_right _ _
    have absurd_le : 1 ≥ 2 := by rwa [h_two_eq_one] at h_ge_two
    have gt21 : 2 > 1 := by decide
    exact (Nat.not_le_of_gt gt21) absurd_le

theorem eq6b.extracted_1_1 :
  q * q ≤ (2 * h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) * (h7.r q hq0 h2mq: ℝ) := by
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) * (h7.n q: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) ^ (h7.n q: ℝ) := ?_
         _ ≤ ((2*h7.m: ℝ)^(h7.r q hq0 h2mq: ℝ)) := ?_
         _ ≤ (2 * ↑h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) * (h7.r q hq0 h2mq: ℝ) := ?_
    · grind
    · norm_cast; exact h7.sq_le_two_mn q h2mq
    · have : (2 * ↑h7.m) * h7.n q ≤ (2 * ↑h7.m) ^h7.n q := by
        refine Nat.mul_le_pow ?_ (h7.n q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (h7.m : ℝ) := by
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity
        exact this
      · norm_cast; exact n_le_r h7 q hq0 h2mq
    · nth_rw 1 [← mul_one (a:= (2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ))]
      apply mul_le_mul (by grind) (mod_cast (h7.one_le_r q hq0 h2mq)) (by grind) (by positivity)

theorem eq6b.extracted_1_2 :
  q * q ≤ (2 * h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) := by
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) * (h7.n q: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) ^ (h7.n q: ℝ) := ?_
         _ ≤ ((2*h7.m: ℝ)^(h7.r q hq0 h2mq: ℝ)) := ?_
    · grind
    · norm_cast; exact h7.sq_le_two_mn q h2mq
    · have : (2 * ↑h7.m) * h7.n q ≤ (2 * ↑h7.m) ^h7.n q := by
        refine Nat.mul_le_pow ?_ (h7.n q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (h7.m : ℝ) := by
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity
        exact this
      · norm_cast
        exact n_le_r h7 q hq0 h2mq

lemma eq6b : (q*q) * ((((h7.c₄ ^ (h7.n q : ℝ) *
  ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)))) *
  (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^q)) ≤
  h7.c₈^(h7.r q hq0 h2mq : ℝ) *
   (h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) + 3/2) := by

    calc
         _ ≤ (((2*h7.m)^(h7.r q hq0 h2mq : ℝ))* ((h7.r q hq0 h2mq)) *
             ((((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)) *
             ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))))) *
             (((h7.c₆* Real.sqrt (2*h7.m) *
             (h7.r q hq0 h2mq: ℝ)^(1/2 : ℝ)) ^(h7.r q hq0 h2mq: ℝ)) *
             ((h7.c₇)^(2*h7.m))^(h7.r q hq0 h2mq: ℝ)))) := ?_

         _ ≤ h7.c₈^(h7.r q hq0 h2mq : ℝ) *
           (h7.r q hq0 h2mq : ℝ)^((h7.r q hq0 h2mq : ℝ) + 3/2) := ?_

    · apply mul_le_mul (eq6b.extracted_1_1 h7 q hq0 h2mq)
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [Real.rpow_natCast]
          refine pow_le_pow_right₀ (one_le_c₄ h7) (n_le_r h7 q hq0 h2mq)
        · apply mul_le_mul
          · exact bound_n_le_r' h7 q hq0 h2mq
          · apply mul_le_mul
            · simp only [Real.rpow_natCast]
              refine pow_le_pow_left₀ ?_ ?_ (h7.r q hq0 h2mq)
              · unfold c₆ house; positivity
              · refine mul_le_mul_of_nonneg_left ?_ ?_
                have := h7.q_eq_sqrtmn q h2mq
                calc _ ≤ √(2 * ↑h7.m) * ↑(h7.n q) ^ (1 / 2 : ℝ) := ?_
                     _ ≤ √(2 * ↑h7.m) * ↑(h7.r q hq0 h2mq) ^ (1 / 2 : ℝ) :=?_
                · rw [this]
                  rw [Real.sqrt_mul]
                  refine mul_le_mul_of_nonneg_left ?_ ?_
                  · rw [le_iff_lt_or_eq]
                    right
                    exact Real.sqrt_eq_rpow ↑(h7.n q)
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
                      Real.sqrt_pos, Nat.ofNat_pos,
                      mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
                  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
                      Nat.cast_nonneg]
                · refine mul_le_mul_of_nonneg_left ?_ ?_
                  · apply Real.rpow_le_rpow
                    · simp only [Nat.cast_nonneg]
                    · simp only [Nat.cast_le]
                      exact n_le_r h7 q hq0 h2mq
                    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
                    Real.sqrt_pos, Nat.ofNat_pos,
                    mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
                · unfold c₆ house; positivity
            · simp only [Real.rpow_natCast]
              rw [← pow_mul]
              refine pow_le_pow_right₀ ?_ ?_
              · exact one_le_c₇ h7
              · trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq) (by positivity) (by positivity)
            · unfold c₇ house; positivity
            · unfold c₆ house; positivity
          · unfold c₇ c₆ house; positivity
          · positivity
        · unfold c₆ c₇ house; positivity
        · simp only [Real.rpow_natCast]
          unfold c₄
          apply pow_nonneg
          simp only [lt_sup_iff, zero_lt_one, true_or,
            mul_nonneg_iff_of_pos_left]
          exact le_trans zero_le_one (h7.one_le_c₃)
      · unfold c₆ c₇ house
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [Real.rpow_natCast]
              · apply mul_nonneg
                · apply pow_nonneg
                  exact zero_le_c₄ h7
                · positivity
            · positivity
          · positivity
      · positivity
    · nth_rw 2 [Real.mul_rpow]
      nth_rw 4 [mul_comm]
      nth_rw 2 [mul_assoc]
      simp only [← mul_assoc]
      nth_rw 3 [mul_assoc]
      nth_rw 1 [← mul_comm]
      rw [mul_comm ((2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ)) (h7.r q hq0 h2mq: ℝ)]
      nth_rw 3 [← Real.rpow_one ((h7.r q hq0 h2mq))]
      simp only [← mul_assoc]
      nth_rw 1  [← Real.rpow_add]
      simp only [mul_assoc]
      rw [← Real.mul_rpow]
      rw [← mul_assoc]
      rw [← mul_assoc]
      nth_rw 8 [mul_comm]
      rw [mul_rotate]
      nth_rw 1 [← mul_assoc]
      nth_rw 1 [← mul_assoc]
      rw [← Real.mul_rpow]
      nth_rw 1 [mul_assoc]
      nth_rw 1 [mul_assoc]
      nth_rw 3 [← mul_assoc]
      nth_rw 1  [← Real.rpow_mul]
      nth_rw 1  [← Real.rpow_add]
      nth_rw 7 [mul_comm]
      simp only [← mul_assoc]
      nth_rw 1 [← Real.mul_rpow]
      apply mul_le_mul
      · unfold c₈
        simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.rpow_natCast, le_refl]
      · ring_nf
        simp only [le_refl]
      · positivity
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · apply h7.c8_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · apply h7.c₆_nonneg
            · simp only [Nat.ofNat_nonneg,
              Real.sqrt_mul, Real.sqrt_pos, Nat.ofNat_pos,
              mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
          · apply pow_nonneg
            · apply h7.c7_nonneg
        · exact zero_le_c₄ h7
      · positivity
      · simp only [Nat.cast_pos]
        apply h7.zero_lt_r
      · simp only [Nat.cast_nonneg]
      · apply mul_nonneg
        · exact c₆_nonneg h7
        · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.sqrt_pos, Nat.ofNat_pos,
          mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · apply mul_nonneg
        · apply pow_nonneg
          · exact c7_nonneg h7
        · exact zero_le_c₄ h7
      · apply pow_nonneg
        · exact c7_nonneg h7
      · exact zero_le_c₄ h7
      · simp only [Nat.cast_pos]
        exact r_qt_0 h7 q hq0 h2mq
      · apply mul_nonneg
        · exact c₆_nonneg h7
        · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.sqrt_pos, Nat.ofNat_pos,
          mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · positivity


lemma eq6 : house (rho h7 q hq0 h2mq) ≤ h7.c₈^(h7.r q hq0 h2mq : ℝ) *
(h7.r q hq0 h2mq : ℝ)^((h7.r q hq0 h2mq : ℝ) + 3/2) := by
  trans
  apply h7.eq6a q hq0 h2mq
  exact h7.eq6b q hq0 h2mq

end Setup

end
