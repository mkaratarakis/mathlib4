/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

--public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainHol

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
  (t : Fin (q * q)) (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

def c₉ : ℝ := Real.exp (|1 + ‖h7.β‖| *  ‖Complex.log h7.α‖ * (↑h7.m : ℝ))

lemma c9_pos : 0 < h7.c₉ := by
  unfold c₉
  apply Real.exp_pos

lemma c9_nonneg : 0 ≤ h7.c₉ := by
  rw [le_iff_lt_or_eq]
  left
  exact c9_pos h7

lemma c9_gt_1 : 1 ≤ h7.c₉ := by
  have := h7.c9_pos
  unfold c₉
  apply Real.one_le_exp
  positivity

variable [DecidableEq (h7.K →+* ℂ)]

variable {z : ℂ} {l₀ : ℝ} (hz : (z : ℂ)
    ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq / q))))
  (hl0 : (l₀ : ℝ) < (h7.m : ℝ) * (1 + h7.r q hq0 h2mq / q))

include hz in
lemma norm_hz : ‖z‖ ≤ ‖(h7.m : ℝ)‖ * ‖1 + (h7.r q hq0 h2mq : ℝ) / (q: ℝ)‖ := by
  simp only [mem_sphere_iff_norm, sub_zero] at hz
  rw [hz]
  simp only [Real.norm_eq_abs]
  apply mul_le_mul
  · simp only [Nat.abs_cast, le_refl]
  · exact le_abs_self (1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))
  · refine Left.add_nonneg ?_ ?_
    · simp only [zero_le_one]
    · refine div_nonneg ?_ ?_
      · simp only [Nat.cast_nonneg]
      · simp only [Nat.cast_nonneg]
  · simp only [Nat.abs_cast, Nat.cast_nonneg]

lemma q_frac : ((↑q + ↑(h7.r q hq0 h2mq)) / ↑q : ℝ ) =
    (1 + ↑(h7.r q hq0 h2mq) / (q : ℝ)) := by
  rw [add_div]
  simp only [add_left_inj]
  refine (div_eq_one_iff_eq ?_).mpr rfl
  simp_all only [ne_eq, Nat.cast_eq_zero]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [lt_self_iff_false]

include hz in
lemma abs_Rb : norm ((h7.R q hq0 h2mq) z) ≤ (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
    (h7.r q hq0 h2mq) ^ (((h7.r q hq0 h2mq : ℝ ) + 1) / 2)) *
    (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := by
  calc _ ≤ ∑ t, ((house ((((algebraMap (𝓞 h7.K) h7.K)
             ((h7.η q hq0 h2mq) t))))) * ‖cexp (h7.ρ q t * z)‖) := ?_
       _ ≤ ∑ t : Fin (q*q), (h7.c₄ ^ (h7.n q : ℝ)) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2)
           * Real.exp ‖(h7.ρ q t * z)‖ := ?_
       _ ≤ ∑ t : Fin (q*q), (h7.c₄ ^ (h7.n q : ℝ)) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) *
           Real.exp (norm ((q : ℝ) * (1 + norm h7.β) * ‖Complex.log h7.α‖ * (h7.m : ℝ) *
           ((1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))))) := ?_
       _ ≤ (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq) ^
           (((h7.r q hq0 h2mq : ℝ ) + 1) / 2)) * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_
  · unfold R
    simp only [canonicalEmbedding.apply_at]
    trans
    apply norm_sum_le
    simp only [Complex.norm_mul]
    apply Finset.sum_le_sum
    intros i hi
    simp only [norm_pos_iff, ne_eq, exp_ne_zero, not_false_eq_true, mul_le_mul_iff_left₀]
    apply norm_embedding_le_house
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := fromlemma82_bound h7 q hq0 i h2mq
      exact lemma82
    · apply Complex.norm_exp_le_exp_norm
    · simp only [norm_nonneg]
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]; apply pow_nonneg; apply h7.zero_le_c₄
      · positivity
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := fromlemma82_bound h7 q hq0 i h2mq
      unfold house at lemma82
      apply Preorder.le_refl _
    · unfold ρ
      --rw [← q_frac]
      simp only [nsmul_eq_mul, norm_mul, Real.exp_le_exp]
      calc
           _ ≤  (‖↑(a q i : ℂ)‖ + ‖↑(b q i) * h7.β‖) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤  (‖(q : ℤ)‖ + ‖q * h7.β‖) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤ (‖(q : ℤ)‖ + ((‖↑(q : ℤ)‖ * ‖h7.β‖))) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ = (‖(q : ℤ)‖ * ((1 + ‖h7.β‖))) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤ ‖(q : ℤ)‖ * ‖1 + ‖h7.β‖‖ * ‖Complex.log h7.α‖* ‖(↑h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := ?_

           _ ≤ ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ * ‖Complex.log h7.α‖ * ‖(↑h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := by
                simp only [mul_assoc]
                simp_all

      · apply mul_le_mul
        · apply mul_le_mul
          · apply norm_add_le
          · apply le_refl
          · simp only [norm_nonneg]
          · refine Left.add_nonneg ?_ ?_
            · simp only [norm_nonneg]
            · simp only [norm_nonneg]
        · simp only [le_refl]
        · simp only [norm_nonneg]
        · apply mul_nonneg
          · refine Left.add_nonneg ?_ ?_
            · simp only [RCLike.norm_natCast, Nat.cast_nonneg]
            · simp only [norm_nonneg]
          · simp only [norm_nonneg]
      · apply mul_le_mul
        · apply mul_le_mul
          · refine add_le_add ?_ ?_
            · simp only [RCLike.norm_natCast, _root_.norm_natCast, Nat.cast_le]
              exact a_le_q q i
            · simp only [Complex.norm_mul, _root_.norm_natCast]
              apply mul_le_mul
              · simp only [Nat.cast_le]
                exact b_le_q q i
              · simp only [le_refl]
              · simp only [norm_nonneg]
              · simp only [Nat.cast_nonneg]
          · simp only [le_refl]
          · simp only [norm_nonneg]
          · refine Left.add_nonneg ?_ ?_
            · simp only [Int.norm_natCast, Nat.cast_nonneg]
            · simp only [norm_nonneg]
        · simp only [le_refl]
        · simp only [norm_nonneg]
        · positivity
      · apply mul_le_mul
        · apply mul_le_mul
          · refine add_le_add ?_ ?_
            · simp only [le_refl]
            · simp only [Complex.norm_mul,
                _root_.norm_natCast, le_refl]
          · simp only [le_refl]
          · simp only [norm_nonneg]
          · positivity
        · simp only [le_refl]
        · simp only [norm_nonneg]
        · positivity
      · congr
        nth_rw 1 [← mul_one (a:=(‖(q : ℤ)‖))]
        rw [mul_add]
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [le_refl]
        · apply mul_le_mul
          · exact le_abs_self (1 + ‖h7.β‖)
          · apply mul_le_mul
            · apply le_refl
            · have := h7.norm_hz q hq0 h2mq hz
              trans
              apply this
              · apply mul_le_mul
                · simp only [Real.norm_natCast, le_refl]
                · simp only [Real.norm_eq_abs]
                  nth_rw 1 [← one_mul (a := |1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)|)]
                  simp only [one_mul, le_refl]
                · positivity
                · positivity
            · simp only [norm_nonneg]
            · simp only [norm_nonneg]
          · positivity
          · simp only [Real.norm_eq_abs, abs_nonneg]
        · positivity
        · simp only [Int.norm_natCast, Nat.cast_nonneg]
      simp only [Real.norm_eq_abs]
      simp only [Nat.abs_cast, abs_norm, le_refl]
    · exact Real.exp_nonneg ‖h7.ρ q i * z‖
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        exact h7.zero_le_c₄
      · apply Real.rpow_nonneg
        simp only [Nat.cast_nonneg]
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul
    · apply Preorder.le_refl
    · apply mul_le_mul
      · apply mul_le_mul
        · simp only [Real.rpow_natCast]
          refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
          left
          exact ⟨one_le_c₄ h7, n_le_r h7 q hq0 h2mq⟩
        · calc _ ≤ (h7.r q hq0 h2mq : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) := ?_
               _ ≤ (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq :ℝ) + 1) / 2) := ?_
          · apply Real.rpow_le_rpow
            · simp only [Nat.cast_nonneg]
            · simp only [Nat.cast_le]; exact n_le_r h7 q hq0 h2mq
            · refine div_nonneg ?_ ?_
              · norm_cast
                simp only [le_add_iff_nonneg_left, zero_le]
              · simp only [Nat.ofNat_nonneg]
          · apply Real.rpow_le_rpow_of_exponent_le
            · simp only [Nat.one_le_cast]
              trans
              apply h7.one_le_n q hq0 h2mq
              exact n_le_r h7 q hq0 h2mq
            · refine (div_le_div_iff_of_pos_right ?_).mpr ?_
              · simp only [Nat.ofNat_pos]
              · simp only [add_le_add_iff_right, Nat.cast_le]
                exact n_le_r h7 q hq0 h2mq
        · apply Real.rpow_nonneg; simp only [Nat.cast_nonneg]
        · apply Real.rpow_nonneg; exact zero_le_c₄ h7
      ·
        rw [Real.rpow_def_of_pos (x:= h7.c₉)]
        · calc _ ≤ Real.exp (
                   |1 + ‖h7.β‖| *  ‖Complex.log h7.α‖ * (↑h7.m) *
                       |(q : ℝ) * (1 + ↑(h7.r q hq0 h2mq) / ↑q)|) := ?_
               _ ≤ Real.exp (Real.log h7.c₉ * (↑(h7.r q hq0 h2mq) + ↑q)) := ?_

          · simp only [Real.exp_le_exp]
            rw [norm_mul];rw [norm_mul];rw [norm_mul];rw [norm_mul]
            have : ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ *  ‖‖Complex.log h7.α‖‖ * ‖(h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖=
                ‖1 + ‖h7.β‖‖ *  ‖‖Complex.log h7.α‖‖ * ‖(h7.m : ℝ)‖ *
              ‖(q : ℝ)‖ * ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := by
                simp only [Real.norm_eq_abs, mul_eq_mul_right_iff, abs_eq_zero]
                left
                rw [mul_assoc, mul_assoc, mul_comm]
                simp only [mul_assoc]
            simp only [mul_assoc] at this
            simp only [mul_assoc]
            rw [this]
            simp only [Real.norm_eq_abs]
            rw [← abs_mul]
            have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
            rw [this]
            simp only [Nat.abs_cast]
            simp only [abs_norm, le_refl]
          · simp only [mul_assoc]
            simp only [Real.exp_le_exp]
            unfold c₉
            simp only [Real.log_exp]
            have : |((h7.r q hq0 h2mq) + q : ℝ)| =
             (↑(h7.r q hq0 h2mq) + ↑q) := by
              simp only [abs_eq_self]
              positivity
            rw [← this]
            simp only [mul_assoc]
            apply mul_le_mul
            · simp only [le_refl]
            · apply mul_le_mul
              · simp only [le_refl]
              · apply mul_le_mul
                · simp only [le_refl]
                · have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
                  rw [this]
                  rw [add_comm]
                · positivity
                · positivity
              · positivity
              · positivity
            · positivity
            · positivity
        · unfold c₉; apply Real.exp_pos
      · positivity
      · apply mul_nonneg
        apply Real.rpow_nonneg
        exact zero_le_c₄ h7
        apply Real.rpow_nonneg
        · positivity
    · simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs]
      apply mul_nonneg
      · apply mul_nonneg
        · apply pow_nonneg
          exact zero_le_c₄ h7
        · positivity
      · apply Real.exp_nonneg
    · positivity

def c₁₀ : ℝ := (2*h7.m* h7.c₄* h7.c₉* h7.c₉^(2*h7.m : ℝ))

lemma c10_nonneg : 0 ≤ h7.c₁₀ := by
  unfold c₁₀
  apply mul_nonneg
  · apply mul_nonneg (mul_nonneg (by positivity) (zero_le_c₄ h7)) (c9_nonneg h7)
  · apply Real.rpow_nonneg; exact c9_nonneg h7

lemma one_le_c10 : 1 ≤ h7.c₁₀ := by
  unfold c₁₀
  simp only [mul_assoc]
  nth_rw 1 [← Real.rpow_one (x := h7.c₉)]
  rw [← Real.rpow_add]
  · apply one_le_mul_of_one_le_of_one_le ?_
    · apply one_le_mul_of_one_le_of_one_le ?_
      · apply one_le_mul_of_one_le_of_one_le ?_
        · refine Real.one_le_rpow (c9_gt_1 h7) ?_
          · refine Left.add_nonneg ?_ ?_
            · simp only [zero_le_one]
            · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
        · exact one_le_c₄ h7
      · simp only [Nat.one_le_cast]; apply h7.one_le_m
    · simp only [Nat.one_le_ofNat]
  · exact c9_pos h7

include hz in
lemma abs_R :(q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
    (h7.r q hq0 h2mq) ^ (((h7.r q hq0 h2mq : ℝ ) + 1) / 2))
     * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ))
         ≤ (h7.c₁₀)^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq : ℝ)^(1/2*((h7.r q hq0 h2mq)+3 : ℝ)) := by
    calc _ ≤ (2*h7.m : ℝ )^(h7.r q hq0 h2mq : ℝ) *(h7.r q hq0 h2mq : ℝ)*
       ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) + 1) / 2))
         * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_
       _ ≤ (h7.c₁₀ ^ (h7.r q hq0 h2mq : ℝ)) *
       (h7.r q hq0 h2mq : ℝ) ^ (1/2 * (h7.r q hq0 h2mq + 3) : ℝ) := ?_
    · apply mul_le_mul
      · apply eq6b.extracted_1_1 h7 q hq0 h2mq
      · simp only [Real.rpow_natCast, le_refl]
      · apply mul_nonneg
        · apply mul_nonneg
          · apply Real.rpow_nonneg
            · exact zero_le_c₄ h7
          · positivity
        · apply Real.rpow_nonneg
          · exact c9_nonneg h7
      · positivity
    · unfold c₁₀
      nth_rw 2 [Real.mul_rpow]
      nth_rw 2 [Real.mul_rpow]
      nth_rw 2 [Real.mul_rpow]
      simp only [← mul_assoc]
      rw [mul_assoc
       ((2*h7.m : ℝ)^(h7.r q hq0 h2mq : ℝ)) (h7.r q hq0 h2mq : ℝ)
       (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ))]
      rw [mul_comm (h7.r q hq0 h2mq : ℝ) (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ))]
      simp only [mul_assoc]
      have hmul :
          (h7.r q hq0 h2mq : ℝ) *
          ((h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) + 1) / 2)
            * h7.c₉ ^ (h7.r q hq0 h2mq + q : ℝ))
          =
          ((h7.r q hq0 h2mq : ℝ) *
            ((h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) + 1) / 2)))
            * h7.c₉ ^ (h7.r q hq0 h2mq + q : ℝ) := by
              rw [mul_assoc]
      rw [hmul]; clear hmul
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · apply mul_le_mul
        · simp only [Real.rpow_natCast, le_refl]
        · rw [Real.rpow_add]
          rw [mul_comm]
          simp only [mul_assoc]
          apply mul_le_mul
          · simp only [Real.rpow_natCast, le_refl]
          · apply mul_le_mul
            · rw [← Real.rpow_mul]
              apply Real.rpow_le_rpow_of_exponent_le
              · exact c9_gt_1 h7
              · norm_cast
                trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul
                · simp only [le_refl]
                · exact n_le_r h7 q hq0 h2mq
                · positivity
                · positivity
              · exact c9_nonneg h7
            · nth_rw 1 [← Real.rpow_one ((h7.r q hq0 h2mq))]
              rw [← Real.rpow_add]
              apply Real.rpow_le_rpow_of_exponent_le
              · simp only [Nat.one_le_cast]
                exact r_qt_0 h7 q hq0 h2mq
              · ring_nf
                simp only [one_div, le_refl]
              · simp only [Nat.cast_pos]
                exact r_qt_0 h7 q hq0 h2mq
            · positivity
            · apply Real.rpow_nonneg
              apply Real.rpow_nonneg
              · exact c9_nonneg h7
          · apply mul_nonneg
            · apply Real.rpow_nonneg
              · exact c9_nonneg h7
            · apply mul_nonneg
              · simp only [Nat.cast_nonneg]
              · apply Real.rpow_nonneg
                · simp only [Nat.cast_nonneg]
          · apply Real.rpow_nonneg
            · exact c9_nonneg h7
          · exact c9_pos h7
        · apply mul_nonneg
          · positivity
          · apply Real.rpow_nonneg
            · exact c9_nonneg h7
        · apply Real.rpow_nonneg
          · exact zero_le_c₄ h7
      · apply mul_nonneg
        · apply Real.rpow_nonneg
          · exact zero_le_c₄ h7
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [Nat.cast_nonneg]
            · apply Real.rpow_nonneg
              · simp only [Nat.cast_nonneg]
          · apply Real.rpow_nonneg
            · exact c9_nonneg h7
      · positivity
      · positivity
      · exact zero_le_c₄ h7
      · apply mul_nonneg
        · positivity
        · exact zero_le_c₄ h7
      · exact c9_nonneg h7
      · apply mul_nonneg
        · apply mul_nonneg
          ·  positivity
          · exact zero_le_c₄ h7
        · exact c9_nonneg h7
      · apply Real.rpow_nonneg
        exact c9_nonneg h7

include hz in
lemma abs_Ra : norm ((h7.R q hq0 h2mq) z) ≤ (h7.c₁₀)^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq : ℝ)^(1/2*((h7.r q hq0 h2mq)+3 : ℝ)) := by
  trans
  apply abs_Rb
  exact hz
  apply abs_R
  exact hz

include hz in
lemma norm_sub_l0_lower_bound_on_sphere :
    (h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ) ≤ ‖z - ((h7.l₀' q hq0 h2mq : ℂ) + 1)‖ := by
  calc _ = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := by ring
       _ ≤ ‖z‖ - ‖(h7.l₀' q hq0 h2mq : ℂ) + 1‖ := by
         have hlm : (h7.l₀' q hq0 h2mq : ℝ) + 1 ≤ h7.m := by
           norm_cast
           apply Fin.isLt
         simp only [mem_sphere_iff_norm, sub_zero] at hz
         rw [hz]
         simp only [tsub_le_iff_right, ge_iff_le]
         have : h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            - ((h7.l₀' q hq0 h2mq : ℝ) + 1) =
           h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            + (- ((h7.l₀' q hq0 h2mq : ℝ) + 1)) := rfl
         norm_cast
         simp only [Nat.cast_add, Nat.cast_one, ge_iff_le]
         rw [this]
         rw [add_assoc]
         simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero]
         exact hlm

       _ ≤ ‖z - ((h7.l₀' q hq0 h2mq : ℂ) + 1)‖ := by
        apply norm_sub_norm_le z

include hz in
lemma norm_z_minus_km_lower_bound_on_sphere (km : Fin (h7.m)) :
  h7.m * h7.r q hq0 h2mq / q ≤ ‖z - ((km: ℂ) + 1)‖  := by
  have hz' :
    ‖z‖ = h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) := by
    simpa [mem_sphere_iff_norm, sub_zero] using hz
  have hkm' : (km : ℝ) ≤ h7.m := le_of_lt (by simp [Nat.cast_lt])
  have hkm : ‖(km : ℂ)‖ ≤ (h7.m : ℝ) := by simp
  calc
  h7.m * h7.r q hq0 h2mq / q
    = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := by ring
  _ = ‖z‖ - norm (h7.m : ℂ) := by simp [hz', sub_eq_add_neg]
  _ ≤ ‖z‖ - ‖(km : ℂ) + 1‖ := by
    simp only [tsub_le_iff_right]
    · rw [sub_eq_add_neg]
      rw [← tsub_le_iff_left]
      rw [sub_eq_add_neg]
      simp only [neg_add_rev, neg_neg, add_neg_cancel_comm_assoc, RCLike.norm_natCast]
      norm_cast
      apply Fin.isLt
  _ ≤ ‖z - ((km : ℂ) + 1)‖ := by
    simp [norm_sub_norm_le z ((km : ℂ) + 1)]

lemma prod_norm_bound : ∏ km ∈ ( {(h7.l₀' q hq0 h2mq : ℕ)}),
        ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖ ≤ (h7.m : ℝ) := by
    simp only [Finset.prod_singleton, sub_self, norm_zero, Nat.cast_nonneg]

lemma prod_bound {ι} (f : ι → ℝ) (s: Finset ι)
  (C : ℝ) (hC : ∀ x ∈ s, 0 ≤ f x)  (h : ∀ x ∈ s, f x ≤ C) :
   ∏ x ∈ (s), f x ≤ C^ Finset.card s := by
    trans
    have : ∏ x ∈ (s), f x ≤ ∏ x ∈ (s), C := by
      apply prod_le_prod
      intros x
      exact fun a ↦ hC x a
      exact fun i a ↦ h i a
    apply this
    simp only [prod_const, le_refl]

def c₁₁ : ℝ := (↑h7.m ^ (h7.m - 1))

lemma one_le_c11 : 1 ≤ h7.c₁₁ := by
  unfold c₁₁
  refine (one_le_pow_iff_of_nonneg ?_ ?_).mpr ?_
  simp only [Nat.cast_nonneg]
  · unfold m; grind
  · norm_cast; exact one_le_m h7

lemma c11_nonneg : 0 ≤ h7.c₁₁ := le_trans zero_le_one (one_le_c11 h7)

include hz h2mq in
lemma abs_denom : norm (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ))) *
      ∏ km ∈ (Finset.range (h7.m) \  {(h7.l₀' q hq0 h2mq : ℕ)} ),
        (((((h7.l₀' q hq0 h2mq : ℂ) + 1 -
        ((km  + 1 : ℂ))) / ((z - ((km + 1 : ℂ))))) ^ (h7.r q hq0 h2mq))))

    ≤ (h7.c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
        (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := by

  let C : ℝ := (h7.m *
       (↑q / (↑h7.m * ↑(h7.r q hq0 h2mq)))) ^ h7.r q hq0 h2mq

  calc
    _ ≤ norm (z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ)} ,
          (((h7.l₀' q hq0 h2mq : ℕ) + 1-
          ((km : ℕ) + 1)) / (z - ((km : ℕ) + 1))) ^ (h7.r q hq0 h2mq)) := ?_

    _ ≤ (h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ)} ,
          (((h7.l₀' q hq0 h2mq : ℕ) + 1-
          ((km : ℕ) + 1)) / (z - ((km : ℕ) + 1))) ^ (h7.r q hq0 h2mq)) := ?_

    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℤ)) *
         ∏ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      (‖(((h7.l₀' q hq0 h2mq: ℕ) + 1 - ((x : ℕ) + 1)) : ℂ)‖ *
       (↑q / (↑h7.m * ↑(h7.r q hq0 h2mq)))) ^ h7.r q hq0 h2mq := ?_

    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℝ)) *

        C ^ Finset.card (Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)})
         := ?_

    _ ≤ (h7.c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
        (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := ?_


  · simp only [zpow_neg, zpow_natCast, Complex.norm_mul,
    norm_inv, norm_pow, norm_prod, Complex.norm_div]
    simp only [add_sub_add_right_eq_sub, le_refl]
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · simp only [zpow_neg, zpow_natCast]
      refine inv_anti₀ ?_ ?_
      · refine pow_pos ?_ (h7.r q hq0 h2mq)
        refine Real.sqrt_ne_zero'.mp ?_
        · refine (Real.sqrt_ne_zero ?_).mpr ?_
          · positivity
          refine div_ne_zero ?_ ?_
          · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
            refine ⟨?_,?_⟩
            · rw [← ne_eq]
              exact Ne.symm (Nat.zero_ne_add_one (2 * h7.h + 1))
            · simp_rw [h7.r_ne_zero]; simp only [not_false_eq_true]
          · have : 0 < (q : ℝ) := by exact mod_cast hq0
            exact Ne.symm (ne_of_lt this)
      · refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (r_ne_zero h7 q hq0 h2mq)).mpr ?_
        · apply h7.norm_z_minus_km_lower_bound_on_sphere q hq0 h2mq hz
    · rw [norm_prod]
  · apply mul_le_mul
    · simp only [zpow_neg, zpow_natCast]
      rw [le_iff_eq_or_lt]
      left
      ring
    · rw [norm_prod]
      apply Finset.prod_le_prod
      intros x hx
      · rw [norm_pow];rw [← norm_pow];positivity
      · intros x hx
        simp only [norm_pow]
        rw [div_eq_mul_inv]
        refine (pow_le_pow_iff_left₀ ?_ ?_ (r_ne_zero h7 q hq0 h2mq)).mpr ?_
        · positivity
        · positivity
        · simp only [Complex.norm_mul]
          apply mul_le_mul
          · simp only [le_refl]
          · simp only [norm_inv]
            simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
            let x' : Fin (h7.m) := ⟨x, hx.1⟩
            have := norm_z_minus_km_lower_bound_on_sphere h7 q hq0 h2mq hz x'
            unfold x' at this
            simp only at this
            simp only [ge_iff_le]
            rw [← one_div_le_one_div]
            · simp only [one_div, inv_div, div_inv_eq_mul, one_mul]
              exact this
            · refine div_pos ?_ ?_
              · norm_cast
              · apply mul_pos
                · unfold m; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                  apply add_pos
                  · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                    unfold h
                    exact Module.finrank_pos
                  · simp only [Nat.ofNat_pos]
                · simp only [Nat.cast_pos]
                  exact r_qt_0 h7 q hq0 h2mq
            · simp only [mem_sphere_iff_norm, sub_zero] at hz
              simp only [inv_pos]
              calc _ < ↑h7.m * ↑(h7.r q hq0 h2mq) / ↑q := ?_
                   _ ≤ ‖z - (↑x + 1)‖ := ?_
              · apply mul_pos
                · apply mul_pos
                  · unfold m; simp only [Nat.cast_add,
                      Nat.cast_mul, Nat.cast_ofNat]
                    apply add_pos
                    · simp only [Nat.ofNat_pos,
                        mul_pos_iff_of_pos_left, Nat.cast_pos]
                      unfold h
                      exact Module.finrank_pos
                    · simp only [Nat.ofNat_pos]
                  · simp only [Nat.cast_pos]
                    exact r_qt_0 h7 q hq0 h2mq
                · simp only [inv_pos, Nat.cast_pos]; exact hq0
              · exact this
          · positivity
          · positivity
    · apply norm_nonneg
    · simp only [zpow_natCast]
      apply pow_nonneg
      simp only [inv_div]
      apply mul_nonneg
      · simp only [Nat.cast_nonneg]
      · simp only [_root_.mul_inv_rev]
        apply mul_nonneg
        · simp only [inv_nonneg, Nat.cast_nonneg]
        · simp only [inv_nonneg, Nat.cast_nonneg]
  · simp only [zpow_natCast]
    simp only [inv_div]
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply prod_bound
      · intros x hx; positivity
      · intros x hx
        unfold C
        refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
        · positivity
        · positivity
        · exact r_ne_zero h7 q hq0 h2mq
        · simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
          have : ‖(h7.l₀' q hq0 h2mq: ℂ) + 1 - (↑x + 1)‖  ≤ (h7.m : ℝ) := by
            simp only [add_sub_add_right_eq_sub]
            rw [← Complex.norm_natCast]
            cases' ((h7.l₀' q hq0 h2mq)) with y hy
            obtain ⟨hx1,hx2⟩ := hx
            simp only [RCLike.norm_natCast]
            by_cases H : x ≤ y
            · have : ‖(y : ℂ) - (x : ℂ)‖ = ((y - x) : ℕ) := by
               rw [← Complex.norm_natCast]
               norm_cast
              rw [this]
              simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
              linarith
            · have : ‖(y : ℂ) - (x : ℂ)‖ = (( x - y ) : ℕ) := by
                calc _ = ‖(x : ℂ) - (y : ℂ)‖ := ?_
                     _ = (( x - y ) : ℕ) := ?_
                · rw [← norm_neg]
                  simp only [neg_sub]
                · rw [← Complex.norm_natCast]
                  have : y ≤ x := by linarith
                  norm_cast
              rw [this]
              simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
              linarith
          apply mul_le_mul
          · simp only [add_sub_add_right_eq_sub] at *
            exact this
          · simp only [le_refl]
          · positivity
          · positivity
    · positivity
    · positivity
  · simp only [inv_div, Real.rpow_natCast]
    have : #(Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}) =
      (h7.m - 1 ) := by
        grind

    rw [this]
    unfold C
    rw [← pow_mul]
    nth_rw 5 [mul_comm]
    rw [mul_pow]
    rw [pow_mul]
    simp only [← mul_assoc]
    nth_rw 2 [mul_comm]
    simp only [mul_assoc]
    rw [← pow_add]
    unfold c₁₁
    have H1 : (h7.r q hq0 h2mq + (((h7.m : ℝ) - 1) : ℝ) * h7.r q hq0 h2mq)=
    (h7.m *h7.r q hq0 h2mq  : ℝ) := by
       ring_nf
    apply mul_le_mul (le_refl _) (?_) (by positivity) (by positivity)
    · simp only [← Real.rpow_natCast]
      have :  ↑(h7.m - 1) = (((h7.m : ℝ) - 1) : ℝ) := by
        refine Nat.cast_pred (by grind)
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [this, H1]
      apply Real.rpow_le_rpow  (by positivity) ?_ (by positivity)
      · refine (div_le_div_iff_of_pos_left ?_ ?_ ?_).mpr ?_
        · simp only [Nat.cast_pos]; exact hq0
        · apply mul_pos
          · simp only [Nat.cast_pos];exact Nat.zero_lt_succ (2 * h7.h + 1)
          · simp only [Nat.cast_pos];exact r_qt_0 h7 q hq0 h2mq
        · simp only [Nat.cast_pos];exact r_qt_0 h7 q hq0 h2mq
        · norm_cast
          nth_rw 1 [← one_mul (a := h7.r q hq0 h2mq)]
          apply mul_le_mul (one_le_m h7) (le_refl _) (Nat.zero_le (h7.r q hq0 h2mq))
            (Nat.zero_le h7.m)

def c₁₂ : ℝ := (2*h7.m : ℝ)^(h7.m/2 : ℝ) * h7.c₁₀ * h7.c₁₁

lemma one_le_c12 : 1 ≤ h7.c₁₂ := by
  unfold c₁₂
  refine one_le_mul_of_one_le_of_one_le ?_ (h7.one_le_c11)
  apply one_le_mul_of_one_le_of_one_le ?_ (h7.one_le_c10)
  · refine Real.one_le_rpow ?_ (by positivity)
    · apply one_le_mul_of_one_le_of_one_le (by aesop) ?_
      · simp only [Nat.one_le_cast]; exact h7.one_le_m

lemma c12_nonneg : 0 ≤ h7.c₁₂ := by
  simpa [c₁₂] using
    mul_nonneg (mul_nonneg (by positivity) (c10_nonneg h7)) h7.c11_nonneg

lemma S_norm_bound : ∀ (hz : z ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))),
  norm (h7.S q hq0 h2mq z) ≤ (h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*
    (h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := by
  intros hz
  calc
    _ = norm ((h7.R q hq0 h2mq z) * ((h7.r q hq0 h2mq).factorial) *
        (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
        ∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
         (((h7.l₀' q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) : ℂ) := ?_

    _ = (h7.r q hq0 h2mq).factorial *
        (norm ((h7.R q hq0 h2mq) z) *
        norm ( (1/(z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (h7.r q hq0 h2mq))) *
        norm ( (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
         (((h7.l₀' q hq0 h2mq + 1)- (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) : ℂ)) := ?_

    _ ≤ (h7.r q hq0 h2mq).factorial *
        ((h7.c₁₀)^(h7.r q hq0 h2mq : ℝ) *
        (h7.r q hq0 h2mq : ℝ)^(1/2*(h7.r q hq0 h2mq + 3 : ℝ)) *
        (h7.c₁₁)^(h7.r q hq0 h2mq : ℝ) *
        (q / h7.r q hq0 h2mq : ℝ)^(h7.m * h7.r q hq0 h2mq : ℝ)) := ?_

    _ ≤ (h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*(h7.r q hq0 h2mq : ℝ) ^
        ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := ?_

  · rw [h7.S_eq_SR_on_circle q hq0 h2mq z hz]
    unfold SR
    simp only [mul_assoc]
  · nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [mul_comm  ↑(h7.r q hq0 h2mq).factorial  ‖h7.R q hq0 h2mq z‖]
    simp only [mul_assoc, zpow_neg, zpow_natCast,
    Complex.norm_mul, norm_natCast, norm_inv, norm_pow,
      norm_prod, Complex.norm_div, one_div]
  · apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · rw [mul_assoc, mul_assoc]
      · apply mul_le_mul (h7.abs_Ra q hq0 h2mq hz) ?_ (by positivity) ?_
        · simp only [one_div, norm_inv, norm_pow, norm_prod, Complex.norm_div]
          have := abs_denom h7 q hq0 h2mq hz
          simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, Real.rpow_natCast] at this
          simp only [Real.rpow_natCast, ge_iff_le]
          exact this
        · apply mul_nonneg (Real.rpow_nonneg (c10_nonneg h7) _) (by positivity)
  · simp only [← mul_assoc]
    rw [mul_comm]
    unfold c₁₂
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    nth_rw 7 [mul_comm]
    simp only [← mul_assoc]
    rw [mul_comm]
    nth_rw 3 [mul_comm]
    ring_nf
    simp only [mul_assoc]
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · calc _ ≤ (Real.sqrt (2*h7.m * h7.r q hq0 h2mq : ℝ))^(h7.r q hq0 h2mq * h7.m : ℝ) *
                 ((↑(h7.r q hq0 h2mq : ℝ))⁻¹ ^ (h7.m * h7.r q hq0 h2mq : ℝ) *
                (h7.r q hq0 h2mq).factorial *
                (h7.r q hq0 h2mq : ℝ)^((1/2 : ℝ)*(h7.r q hq0 h2mq + 3 : ℝ))) := ?_

             _≤ (Real.sqrt (2*h7.m : ℝ)^((h7.m * h7.r q hq0 h2mq : ℝ)) *
                ((h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ))^((h7.m * h7.r q hq0 h2mq : ℝ)))*
                ((h7.r q hq0 h2mq : ℝ)^(h7.r q hq0 h2mq : ℝ) *
                (↑(h7.r q hq0 h2mq : ℝ))⁻¹ ^ (h7.m * h7.r q hq0 h2mq : ℝ) *
                (h7.r q hq0 h2mq : ℝ)^((1/2 : ℝ)*(h7.r q hq0 h2mq + 3 : ℝ))) :=?_

             _= ((↑h7.m * 2 : ℝ) ^ ((h7.m : ℝ) * (1 / 2: ℝ))) ^ (h7.r q hq0 h2mq : ℝ)*

              (h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := ?_

        · rw [Real.mul_rpow]
          simp only [mul_assoc]
          apply mul_le_mul
          have := h7.sqt_etc q hq0 h2mq
          have := h7.q_le_2sqrtmr q hq0 h2mq
          apply Real.rpow_le_rpow
          · simp only [Nat.cast_nonneg]
          · rw [h7.q_eq_sqrtmn q h2mq]
            simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg,
              Real.sqrt_mul, Nat.ofNat_nonneg]
            simp only [mul_assoc]
            apply mul_le_mul
            · simp only [le_refl]
            · apply mul_le_mul
              · simp only [le_refl]
              · simp only [Nat.cast_nonneg, Real.sqrt_le_sqrt_iff, Nat.cast_le]
                exact n_le_r h7 q hq0 h2mq
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · ring_nf
            simp only [one_div, le_refl]
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [h7.sqt_etc q hq0 h2mq]
          rw [Real.mul_rpow]
          apply mul_le_mul
          · rw [mul_comm (h7.m : ℝ) (h7.r q hq0 h2mq : ℝ)]
          · rw [mul_comm]
            nth_rw 5 [mul_comm]
            apply mul_le_mul
            · simp only [le_refl]
            · rw [mul_comm]
              apply mul_le_mul
              · norm_cast
                exact Nat.factorial_le_pow (h7.r q hq0 h2mq)
              · simp only [le_refl]
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [← Real.rpow_mul]
          rw [← Real.rpow_mul]
          rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul]
          rw [mul_comm (h7.m : ℝ) (1/2)]
          rw [mul_comm (h7.m : ℝ) 2]
          simp only [mul_assoc]
          congr
          rw [Real.inv_rpow]
          rw [← mul_assoc]
          rw [← Real.rpow_add]
          rw [← Real.rpow_neg]
          rw [← Real.rpow_add]
          rw [← Real.rpow_add]
          · ring_nf
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
          · positivity
          · simp only [Nat.cast_nonneg]
        · ring_nf
          simp only [one_div, Real.rpow_natCast, le_refl]
      · positivity
      · apply Real.rpow_nonneg
        apply h7.c10_nonneg
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact c10_nonneg h7
      · positivity
    · apply Real.rpow_nonneg
      exact h7.c11_nonneg
    · positivity
    · exact c10_nonneg h7
    · apply mul_nonneg
      · positivity
      · exact c10_nonneg h7
    · apply c11_nonneg

include u t in
lemma eq7 (l' : Fin (h7.m)) :
  ρᵣ h7 q hq0 h2mq = Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq) : ℤ) *
    ((2 * ↑Real.pi * I)⁻¹ *
      (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq / q))),
        (z - (h7.l₀' q hq0 h2mq + 1))⁻¹ * (h7.S q hq0 h2mq) z)) := by
  calc _ = (Complex.log (h7.α)) ^ (-(h7.r q hq0 h2mq) : ℤ)
       * (h7.S q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) := ?_
       _ = (Complex.log (h7.α)) ^ (-(h7.r q hq0 h2mq) : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq) / q)),
     (z - (h7.l₀' q hq0 h2mq + 1))⁻¹ * (h7.S q hq0 h2mq) z)) := ?_
  · apply sys_coeff_foo_S h7 q hq0 h2mq
  · have := h7.hcauchy q hq0 h2mq
    rw [this]

def c₁₃ : ℝ :=((‖Complex.log h7.α‖⁻¹ + 1)*h7.m*(2 + 1/h7.m)*h7.c₁₂)

lemma c13_nonneg : 0 ≤ h7.c₁₃ := by
  unfold c₁₃
  apply mul_nonneg (by positivity) (h7.c12_nonneg)

lemma one_le_c13 : 1 ≤ h7.c₁₃ := by
  unfold c₁₃
  have : 1 ≤ h7.c₁₂ := h7.one_le_c12
  refine one_le_mul_of_one_le_of_one_le ?_ (this)
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · rw [add_comm]
      refine le_add_of_le_of_nonneg (le_refl _) (by positivity)
    · simp only [Nat.one_le_cast]; exact Nat.le_of_ble_eq_true rfl
  · simp only [one_div]
    refine le_add_of_le_of_nonneg (by aesop) (by positivity)

def Cnum : ℝ := ((h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ))⁻¹ *
  ((h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*(h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)*
              (((3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))))

lemma hf : ∀ z ∈ Metric.sphere 0 (h7.m * (1 + ↑(h7.r q hq0 h2mq : ℝ) / ↑q)),
    ‖(z - ((↑(h7.l₀' q hq0 h2mq) : ℂ) + 1))⁻¹ *
    (h7.S q hq0 h2mq z)‖ ≤ h7.Cnum q hq0 h2mq := by
      intros z hz
      have hS := S_norm_bound h7 q hq0 h2mq hz
      simp only [Complex.norm_mul, norm_inv, ge_iff_le]
      --have := h7.S_eq_SR_on_circle q hq0 h2mq z hz
      --rw [← this]
      unfold Cnum
      apply mul_le_mul
      · apply inv_anti₀
        · refine Real.sqrt_ne_zero'.mp ?_
          · refine (Real.sqrt_ne_zero ?_).mpr ?_
            positivity
            refine div_ne_zero ?_ ?_
            · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
              constructor
              · rw [← ne_eq]; unfold m
                simp only [ne_eq, Nat.add_eq_zero_iff, mul_eq_zero,
                 OfNat.ofNat_ne_zero, false_or,
                  and_false, not_false_eq_true]
              · simp_rw [h7.r_ne_zero]; simp only [not_false_eq_true]
            · have : 0 < (q : ℝ) := by exact mod_cast hq0
              exact Ne.symm (ne_of_lt this)
        apply h7.norm_sub_l0_lower_bound_on_sphere q hq0 h2mq hz
      · exact hS
      · positivity
      · positivity


include u t in
lemma eq8 : norm (ρᵣ h7 q hq0 h2mq) ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := by

  have hR : 0 ≤ (h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q) : ℝ) := by
    apply mul_nonneg
    · simp only [Nat.cast_nonneg]
    · trans
      · exact zero_le_one
      · simp only [le_add_iff_nonneg_right]
        have := h7.r_div_q_geq_0 q hq0 h2mq
        have : 0 ≤ (h7.r q hq0 h2mq : ℝ) := by simp only [Nat.cast_nonneg]
        apply div_nonneg
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_nonneg]

  have H := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
    (h7.hf q hq0 h2mq)

  calc _ = norm (Complex.log h7.α ^ (-(h7.r q hq0 h2mq : ℤ))
  * ((2 * Real.pi) * I)⁻¹ * ∮ (z : ℂ) in
           C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
           (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)) := ?_

       _ = norm (Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ))) *
          norm ((2 * Real.pi * I)⁻¹) * norm (∮ (z : ℂ) in
          C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
          (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)) := ?_

       _ ≤ ((norm ((Complex.log h7.α))^ (-(h7.r q hq0 h2mq : ℤ)))) *
         (h7.m : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) *
          (h7.c₁₂) ^ (h7.r q hq0 h2mq : ℝ) *
          ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           (3 - h7.m : ℝ) / 2 + 3 / 2) * ((q : ℝ) / (((h7.m : ℝ) *
            (h7.r q hq0 h2mq : ℝ))))) := ?_

       _ ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := ?_

  · rw [h7.eq7 q hq0 u t h2mq]
    simp only [mul_assoc]
    exact (h7.l₀' q hq0 h2mq)
  · simp only [zpow_neg, zpow_natCast, _root_.mul_inv_rev,
    norm_inv, norm_pow, norm_real, Real.norm_eq_abs, norm_ofNat, norm_mul]
  · simp only [mul_assoc]
    simp only [zpow_neg, zpow_natCast, norm_inv, norm_pow, _root_.mul_inv_rev, inv_I, neg_mul,
      norm_neg, Complex.norm_mul, norm_I, norm_real, Real.norm_eq_abs, one_mul, norm_ofNat]
    · apply mul_le_mul
      · simp only [le_refl]
      · simp only [_root_.mul_inv_rev, inv_I, neg_mul, smul_eq_mul, norm_neg, Complex.norm_mul,
          norm_I, norm_inv, norm_real, Real.norm_eq_abs, norm_ofNat, one_mul] at H
        simp only [mul_assoc] at *
        trans
        apply H
        simp only [Real.rpow_natCast]
        apply mul_le_mul
        · simp only [le_refl]
        · unfold Cnum
          --simp only [← mul_assoc]
          nth_rw 2 [mul_comm]
          simp only [mul_assoc]
          simp only [Real.rpow_natCast, inv_div]
          ring_nf;
          simp only [le_refl]
        · unfold Cnum
          apply mul_nonneg
          · positivity
          · apply mul_nonneg
            · positivity
            · apply mul_nonneg
              · apply Real.rpow_nonneg
                · exact c12_nonneg h7
              · positivity
        · simp only [Nat.cast_nonneg]
      · positivity
      · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
  · simp only [zpow_neg, zpow_natCast, mul_assoc]
    nth_rw 5 [← mul_comm]
    unfold c₁₃
    rw [Real.mul_rpow, Real.mul_rpow, Real.mul_rpow]
    simp only [mul_assoc]
    apply mul_le_mul
    · rw [← norm_inv, ← inv_pow, ← norm_inv]
      simp only [Real.rpow_natCast]
      apply pow_le_pow_left₀
      simp only [norm_inv, inv_nonneg, norm_nonneg]
      simp only [norm_inv, le_add_iff_nonneg_right, zero_le_one]
    · apply mul_le_mul
      · nth_rw 1 [← Real.rpow_one (x:= h7.m)]
        apply Real.rpow_le_rpow_of_exponent_le
        · unfold m; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          rw [le_iff_lt_or_eq]
          left
          trans
          apply one_lt_two
          simp only [lt_add_iff_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
          unfold h; exact Module.finrank_pos
        · simp only [Nat.one_le_cast]
          exact one_le_r h7 q hq0 h2mq
      · simp only [← mul_assoc]
        nth_rw 1 [mul_comm]
        nth_rw 6 [mul_comm]
        apply mul_le_mul
        · simp only [le_refl]
        · simp only [mul_assoc]
          rw [mul_comm]
          nth_rw 4 [mul_comm]
          simp only [mul_assoc]
          apply mul_le_mul ?_ ?_ (by positivity) (Real.rpow_nonneg (c12_nonneg h7) _)
          · simp only [Real.rpow_natCast, le_refl]
          · ring_nf
            rw [mul_rotate]
            simp only [mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            nth_rw 1 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            calc _ ≤ (h7.m : ℝ)⁻¹ + (2*(h7.m : ℝ)*(h7.r q hq0 h2mq : ℝ))
                      * ((h7.m : ℝ)⁻¹ * (h7.r q hq0 h2mq : ℝ)⁻¹) :=?_
                 _ ≤ (2 + (h7.m : ℝ)⁻¹) ^ (h7.r q hq0 h2mq : ℝ) := ?_
            · simp only [add_le_add_iff_left]
              apply mul_le_mul ?_ (le_refl _) (by positivity) (by positivity)
              · norm_cast
                trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq) (by positivity) (by positivity)
            · ring_nf
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              nth_rw 1 [← Real.rpow_one (x:=(2 + (h7.m : ℝ)⁻¹))]
              apply Real.rpow_le_rpow_of_exponent_le
              · refine le_add_of_le_of_nonneg ?_ (by positivity)
                · simp only [Nat.one_le_ofNat]
              · simp only [Nat.one_le_cast]
                exact one_le_r h7 q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]; exact r_ne_zero h7 q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]
                exact Nat.ne_zero_of_lt (h7.one_le_m)
            · simp only [ne_eq, Nat.cast_eq_zero];exact r_ne_zero h7 q hq0 h2mq
            · simp only [ne_eq, Nat.cast_eq_zero]
              exact Nat.ne_zero_of_lt hq0
        · apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · apply Real.rpow_nonneg (c12_nonneg h7)
          · positivity
        · positivity
      · apply mul_nonneg
        · positivity
        · apply mul_nonneg
          · apply Real.rpow_nonneg (c12_nonneg h7)
          · positivity
      · positivity
    · apply mul_nonneg (by positivity)
      · apply mul_nonneg (by positivity)
          (mul_nonneg (Real.rpow_nonneg (c12_nonneg h7) _) (by positivity))
    · apply Real.rpow_nonneg
      rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · simp only [Nat.cast_nonneg]
    · positivity
    · positivity
    · positivity
    · exact c12_nonneg h7


def c₁₄ : ℝ := (h7.c₈^((h7.h-1)) * h7.c₁₃)

lemma c14_nonneg : 1 ≤ h7.c₁₄ :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ h7.c8_geq_one) h7.one_le_c13

include u t in
lemma use6and8 :
  norm ((Algebra.norm ℚ (rho h7 q hq0 h2mq))) ≤ (h7.c₁₄)^(h7.r q hq0 h2mq : ℝ) *
  (h7.r q hq0 h2mq : ℝ)^((-(h7.r q hq0 h2mq : ℝ))/2 + 3 * (h7.h)/2) := by

  calc _ ≤  ‖ρᵣ h7 q hq0 h2mq‖ * (house (rho h7 q hq0 h2mq)) ^ (((h7.h) - 1 )) := ?_

       _ ≤ (h7.c₈ ^ h7.r q hq0 h2mq * ↑(h7.r q hq0 h2mq :ℝ) ^
          ((h7.r q hq0 h2mq : ℝ) + 3 / 2))^((h7.h) -1) *
          ((h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2))) := ?_

       _ ≤ ((h7.c₁₄)^(h7.r q hq0 h2mq : ℝ)) * (↑(h7.r q hq0 h2mq: ℝ))^(
         (((h7.h: ℝ) - 1)) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
         ((((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ))) / 2) + 3 / 2)) := ?_

       _ = ((h7.c₁₄)^(h7.r q hq0 h2mq: ℝ)) * (↑(h7.r q hq0 h2mq: ℝ))^(
         ((-(h7.r q hq0 h2mq : ℝ))/2) + 3 * (h7.h)/ 2) := ?_

  · have := norm_norm_le_norm_mul_house_pow (K := h7.K) (α := (h7.rho q hq0 h2mq)) h7.σ
    rw [← rho_eq_ρᵣ]
    unfold h
    simp only [← Real.rpow_natCast] at *
    exact this
  · nth_rw 2 [mul_comm]
    apply mul_le_mul
    · apply eq8 h7 q hq0 u t h2mq
    · have := h7.eq6 q hq0 h2mq
      simp only [← Real.rpow_natCast] at *
      apply Real.rpow_le_rpow
      · exact house_nonneg (h7.rho q hq0 h2mq)
      · exact this
      · simp only [Nat.cast_nonneg]
    · apply pow_nonneg; exact house_nonneg (h7.rho q hq0 h2mq)
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact h7.c13_nonneg
      · positivity
  · unfold c₁₄
    simp only [← Real.rpow_natCast] at *
    rw [Real.mul_rpow]
    rw [← Real.rpow_mul]
    nth_rw 3 [mul_comm]
    nth_rw 1 [← Real.rpow_mul]
    nth_rw 5 [mul_comm]
    simp only [← mul_assoc]
    nth_rw  2 [mul_assoc]
    rw [← Real.rpow_add]
    rw [mul_comm]
    simp only [← mul_assoc]
    rw [Real.rpow_mul]
    rw [← Real.mul_rpow]
    nth_rw 7 [mul_comm]
    nth_rw 2 [mul_comm]
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      simp only [le_refl]
    · rw [le_iff_lt_or_eq]
      right
      congr
      refine Nat.cast_pred ?_
      unfold h; exact Module.finrank_pos
    · positivity
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      apply mul_nonneg
      · apply pow_nonneg
        exact c8_nonneg h7
      · exact h7.c13_nonneg
    · exact h7.c13_nonneg
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg h7
    · exact c8_nonneg h7
    · simp only [Nat.cast_pos]
      exact r_qt_0 h7 q hq0 h2mq
    · simp only [Nat.cast_nonneg]
    · exact c8_nonneg h7
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg h7
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
  · unfold m
    simp only [mul_eq_mul_left_iff]
    left
    have :((h7.h: ℝ) - 1) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
      ((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ)) / 2 + 3 / 2)=
    (-(h7.r q hq0 h2mq : ℝ))/2 + 3 * (h7.h)/ 2 := by
      unfold m
      rw [mul_add]
      rw [← add_div]
      rw [← add_div]
      rw [mul_div]
      rw [add_assoc]
      rw [← add_div]
      rw [add_div']
      apply Mathlib.Tactic.LinearCombination.div_eq_const
      · rw [mul_sub]
        rw [sub_mul]
        rw [sub_mul]
        rw [sub_mul]
        simp only [one_mul]
        simp only [sub_add_add_cancel]
        ring_nf
        simp only [add_assoc]
        nth_rw 2 [sub_eq_add_neg]
        simp only [add_right_inj]
        rw [sub_eq_add_neg]
        simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
        rw [mul_add]
        ring
      · simp only [ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true]
    rw [← this]
    unfold m
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

def c₁₅ : ℝ := h7.c₁₄ * h7.c₅

lemma c15_nonneg :  0 ≤ h7.c₁₅ := by
  unfold c₁₅
  apply mul_nonneg
  · apply le_trans (zero_le_one) (h7.c14_nonneg)
  · rw [le_iff_lt_or_eq]
    left
    exact c5nonneg h7

lemma c15_geg_1 : 1 ≤ h7.c₁₅ := by
  unfold c₁₅
  refine one_le_mul_of_one_le_of_one_le (h7.c14_nonneg)
    (by
      unfold c₅
      refine one_le_pow₀ ?_
      simp_all only [Int.cast_abs, le_add_iff_nonneg_left, abs_nonneg]
      )

theorem norm_pos_rho  :
    0 < ‖(Algebra.norm ℚ) (h7.rho q hq0 h2mq)‖ := by
  simp only [norm_pos_iff, ne_eq, Algebra.norm_eq_zero_iff]
  intros H
  apply_fun h7.σ at H
  apply ρᵣ_nonzero h7 q hq0 h2mq
  rw [rho_eq_ρᵣ] at H
  simp only [H, map_zero]

lemma eq5inv:
  norm ((Algebra.norm ℚ) (h7.rho q hq0 h2mq)) ⁻¹ <
    h7.c₅ ^ ((h7.r q hq0 h2mq : ℝ)) := by
  have eq5 := eq5 h7 q hq0 h2mq
  simp only at eq5
  rw [← inv_lt_inv₀] at eq5
  · simp only [norm_inv]
    simp only at eq5
    rw [← Real.rpow_neg] at eq5
    simp only [neg_neg] at eq5
    exact eq5
    rw [le_iff_lt_or_eq]
    left
    exact c5nonneg h7
  · exact norm_pos_rho h7 q hq0 h2mq
  · simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pos]
    apply pow_pos
    apply c5nonneg h7

include u t in
lemma use5 : (h7.r q hq0 h2mq : ℝ) ^
  (((h7.r q hq0 h2mq : ℝ) - 3 * (h7.h)) / 2) <
    (h7.c₁₅) ^ (h7.r q hq0 h2mq : ℝ) := by

  have eq5 := eq5 h7 q hq0 h2mq

  have Hpow : ↑(h7.r q hq0 h2mq : ℝ) ^
    (((h7.r q hq0 h2mq : ℝ ) - 3 * h7.h) / 2) =
    (↑(h7.r q hq0 h2mq : ℝ) ^
    (-(h7.r q hq0 h2mq : ℝ ) / 2 + 3 * ↑h7.h / 2))⁻¹ := by
    rw [← one_div]
    ring_nf
    rw [← Real.rpow_neg]
    congr
    ring_nf
    simp only [Nat.cast_nonneg]
  have :  ↑(h7.r q hq0 h2mq : ℝ) ^
    (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2) ≤
    (norm (↑((Algebra.norm ℚ) (h7.rho q hq0 h2mq))) ⁻¹)
      * h7.c₁₄ ^ (h7.r q hq0 h2mq : ℝ):= by
    simp only [norm_inv]
    refine (le_inv_mul_iff₀' (norm_pos_rho h7 q hq0 h2mq)).mpr ?_
    · rw [Hpow]
      refine inv_mul_le_of_le_mul₀ (by positivity) ?_ ?_
      · apply Real.rpow_nonneg (le_trans zero_le_one h7.c14_nonneg)
      · trans
        apply (use6and8 h7 q hq0 u t h2mq)
        rw [mul_comm]
  calc _ = (↑(h7.r q hq0 h2mq : ℝ) ^
     (-(h7.r q hq0 h2mq : ℝ ) / 2 + 3 * ↑h7.h / 2))⁻¹ := ?_
       _ ≤ (norm (↑((Algebra.norm ℚ) (h7.rho q hq0 h2mq))))⁻¹
           * h7.c₁₄ ^ (h7.r q hq0 h2mq : ℝ) := ?_
       _ < h7.c₁₄^(h7.r q hq0 h2mq : ℝ) * h7.c₅ ^(h7.r q hq0 h2mq : ℝ) := ?_
       _ = (h7.c₁₅) ^(h7.r q hq0 h2mq : ℝ) := ?_
  · rw [← Hpow]
  · simp only at this
    rw [← Hpow]
    simp only [norm_inv] at this
    apply this
  · rw [mul_comm]
    have := eq5inv h7 q hq0 h2mq
    simp only [norm_inv, Real.rpow_natCast] at this
    refine (mul_lt_mul_iff_right₀ ?_).mpr ?_
    · simp only [Real.rpow_natCast]
      apply pow_pos
      have := h7.c14_nonneg
      linarith
    · simp only [Real.rpow_natCast]
      exact this
  · unfold c₁₅
    rw [← Real.mul_rpow]
    · exact le_trans zero_le_one h7.c14_nonneg
    · exact (c5nonneg h7).le

theorem gelfondSchneider (α β : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
  (htriv : α ≠ 0 ∧ α ≠ 1) (hirr : ∀ i j : ℤ, β ≠ i / j) :
    Transcendental ℚ (α ^ β) := fun hγ => by

  obtain ⟨K, hK, hNK, σ, hd, α', β', γ', habc⟩ :=
    exists_common_field_of_isAlgebraic α β (α^β) hα hβ hγ

  have h7 : Setup :=
    Setup.mk α β K σ α' β' γ' hirr htriv hα hβ habc hd

  haveI : DecidableEq (h7.K →+* ℂ) := h7.hd

  let q : ℕ := 2 * h7.m * ((6 * h7.h) * Nat.ceil ( (h7.c₁₅)^4))

  have hq0 : 0 < q := by
    unfold q
    simp only [CanonicallyOrderedAdd.mul_pos, Nat.ofNat_pos, Nat.ceil_pos,true_and]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), ?_⟩
    refine ⟨?_, ?_⟩
    · unfold h; exact Module.finrank_pos
    · apply pow_pos
      have := h7.c15_geg_1
      linarith

  have h2mq : 2 * h7.m ∣ q ^ 2 := by
    unfold q
    rw [pow_two]
    refine Nat.mul_dvd_mul ?_ ?_
    · simp only [mul_assoc]
      exact Nat.dvd_mul_right 2 (h7.m * (6 * (h7.h * ⌈h7.c₁₅ ^ 4⌉₊)))
    · nth_rw 2 [mul_comm]
      simp only [mul_assoc]
      exact Nat.dvd_mul_right h7.m (2 * (6 * (h7.h * ⌈h7.c₁₅ ^ 4⌉₊)))

  let u : Fin (h7.m * h7.n q) := ⟨0, by
    apply mul_pos; exact Nat.zero_lt_succ (2 * h7.h + 1); unfold n;
    apply Nat.div_pos (qsqrt_le_2m h7 q hq0 h2mq) ?_
    · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      exact Nat.zero_lt_succ (2 * h7.h + 1)⟩

  let t : Fin (q * q) := ⟨0, by apply mul_pos; exact hq0; exact hq0⟩

  have use5 := use5 h7 q hq0 u t h2mq

  have hnr : (h7.n q : ℝ) ≤ (h7.r q hq0 h2mq : ℝ) :=
    mod_cast n_le_r h7 q hq0 h2mq

  have H1 : (2*h7.m) * (6* h7.h) ≤ q := by
    unfold q
    apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · nth_rw 1 [← mul_one (a:= (6* h7.h))]
      apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
      · simp only [Nat.one_le_ceil_iff];
        apply pow_pos
        have := h7.c15_geg_1
        linarith

  have H2 : (2*h7.m) * (h7.c₁₅)^4 ≤ q := by
    unfold q
    simp only [mul_assoc]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀]
    apply mul_le_mul (le_refl _)
    · nth_rw 1 [← one_mul (a := (h7.c₁₅ ^ 4) )]
      nth_rw 1 [← mul_assoc]
      apply mul_le_mul ?_ (Nat.le_ceil (h7.c₁₅ ^ 4)) (by positivity) (by positivity)
      · unfold h;
        refine one_le_mul_of_one_le_of_one_le ?_ ?_
        · simp only [Nat.one_le_ofNat]
        · norm_cast
          have : 0 < h7.h := by
            unfold h; exact Module.finrank_pos
          unfold h at *
          linarith
    · apply pow_nonneg
      have := h7.c15_geg_1
      grind
    · positivity

  have H3 : 6* h7.h ≤ h7.n q := by
    unfold n
    calc _ ≤ ((2*h7.m) * (6* h7.h))^2 /(2 * h7.m) := ?_
         _ ≤  h7.n q := ?_
    · refine (Nat.le_div_iff_mul_le ?_).mpr ?_
      · have : 0 < h7.h := by
          unfold h; exact Module.finrank_pos
        unfold h at *
        apply mul_pos (by aesop) (Nat.zero_lt_succ (2 * h7.h + 1))
      · rw [mul_comm, Nat.pow_two]
        apply Nat.le_mul_self
    · unfold n q
      refine Nat.div_le_div_right (Nat.pow_le_pow_left H1 2)

  have H4 : (h7.c₁₅)^4 ≤ (h7.n q : ℝ) := by
    unfold n q
    refine Nat.ceil_le.mp ?_
    refine (Nat.le_div_iff_mul_le ?_).mpr ?_
    · have : 0 < h7.h := by
        unfold h; exact Module.finrank_pos
      unfold h at *
      apply mul_pos (by aesop) (Nat.zero_lt_succ (2 * h7.h + 1))
    · rw [mul_comm, mul_pow]
      apply mul_le_mul
      · rw [Nat.pow_two]; apply Nat.le_mul_self
      · rw [Nat.pow_two]
        simp only [← mul_assoc]
        nth_rw 2 [mul_comm]
        simp only [← mul_assoc]
        nth_rw 2 [mul_comm]
        simp only [mul_assoc]
        nth_rw 1 [← one_mul (a := ⌈h7.c₁₅ ^ 4⌉₊)]
        rw [← Nat.pow_two]
        simp only [← mul_assoc]
        apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · have : 0 < h7.h := by
            unfold h; exact Module.finrank_pos
          unfold h at *
          refine Nat.one_le_iff_ne_zero.mpr ?_
          refine Nat.mul_ne_zero_iff.mpr ?_
          · constructor
            · simp only [ne_eq, mul_eq_zero,
               OfNat.ofNat_ne_zero, false_or, or_false]
              rw [← ne_eq]
              exact Nat.ne_zero_of_lt this
            · exact Nat.ne_zero_of_lt this
        · rw [Nat.pow_two]; apply Nat.le_mul_self
      · positivity
      · positivity

  have H5 : 6* h7.h ≤ h7.r q hq0 h2mq := by
    trans
    apply H3
    exact (n_le_r h7 q hq0 h2mq)

  have H6 : (h7.c₁₅)^4 ≤ h7.r q hq0 h2mq := by
    trans
    apply H4
    simp only [Nat.cast_le]
    exact n_le_r h7 q hq0 h2mq

  apply absurd
  · apply use5
  · simp only [Real.rpow_natCast, not_lt]
    rw [← Real.rpow_le_rpow_iff (z:= ( ((↑(h7.r q hq0 h2mq) - 3 * ↑h7.h) / 2) : ℝ)⁻¹)]
    rw [← Real.rpow_mul, mul_inv_cancel₀]
    simp only [inv_div, Real.rpow_one]
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    have : h7.c₁₅ ^ ((h7.r q hq0 h2mq : ℝ) * (2 / (↑(h7.r q hq0 h2mq) - 3 * ↑h7.h))) ≤
       h7.c₁₅ ^ (4 : ℝ)  := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact c15_geg_1 h7
        · rw [mul_div]
          ring_nf
          simp only [mul_assoc]
          rw [mul_comm]
          simp only [mul_assoc]
          refine (inv_mul_le_iff₀' ?_).mpr ?_
          · calc _ < ↑h7.h * 3 := ?_
                 _ ≤ ((h7.h * 6 - ↑h7.h * 3) : ℝ) := ?_
                 _ ≤ (h7.r q hq0 h2mq : ℝ) - h7.h * 3 := ?_
            · have : 0 < h7.h := by
                unfold h; exact Module.finrank_pos
              unfold h at *
              simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, Nat.cast_pos, gt_iff_lt]
              linarith
            · ring_nf; simp only [le_refl]
            · simp only [tsub_le_iff_right, sub_add_cancel]
              rw [mul_comm]
              norm_cast
          · rw [sub_eq_neg_add]
            rw [mul_add]
            simp only [mul_neg, le_neg_add_iff_add_le]
            calc _ ≤  2 *  (6 * (↑h7.h)) + 2 * (h7.r q hq0 h2mq : ℝ) := ?_
                 _ ≤  2 * (h7.r q hq0 h2mq : ℝ) + 2 * (h7.r q hq0 h2mq : ℝ) := ?_
                 _ ≤  4 * (h7.r q hq0 h2mq : ℝ) := ?_

            · simp only [add_le_add_iff_right]; ring_nf; simp only [le_refl]
            · simp only [add_le_add_iff_right]
              apply mul_le_mul (le_refl _) (by norm_cast) (by positivity) (by positivity)
            · ring_nf; simp only [le_refl]
    trans
    apply this
    simp only [Real.rpow_ofNat]
    apply H6
    · exact c15_nonneg h7
    · have Hh : 0 < h7.h := by unfold h; exact Module.finrank_pos
      apply div_ne_zero
      · have : 3 * h7.h < (h7.r q hq0 h2mq : ℝ) := by
          calc _ < (6 * h7.h : ℝ)  := by norm_cast; grind
               _ ≤ (h7.r q hq0 h2mq :ℝ) := by norm_cast;
        grind
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · positivity
    · apply pow_nonneg (c15_nonneg h7)
    · positivity
    · have Hh : 0 < h7.h := by unfold h; exact Module.finrank_pos
      unfold h at *
      simp only [inv_div, Nat.ofNat_pos, div_pos_iff_of_pos_left, sub_pos, gt_iff_lt]
      have : 3 * h7.h < (h7.r q hq0 h2mq : ℝ) := by
          calc _ < (6 * h7.h : ℝ)  := ?_
               _ ≤ (h7.r q hq0 h2mq : ℝ) := by norm_cast
          · norm_cast
            refine Nat.mul_lt_mul_of_pos_right ?_ Hh; simp only [Nat.reduceLT]
      unfold h at *
      exact this

end Setup


end
