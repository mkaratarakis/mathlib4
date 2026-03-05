/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
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

lemma c9_pos : 0 < h7.c₉ := Real.exp_pos _

lemma c9_nonneg : 0 ≤ h7.c₉ := by
  rw [le_iff_lt_or_eq]
  left
  exact Real.exp_pos _

lemma c9_gt_1 : 1 ≤ h7.c₉ := by
  apply Real.one_le_exp
  positivity

def c₁₁ : ℝ := (↑h7.m ^ (h7.m - 1))

lemma one_le_c11 : 1 ≤ h7.c₁₁ :=
  (one_le_pow_iff_of_nonneg (by simp) (by unfold m; grind)).mpr (mod_cast h7.one_le_m)

lemma c11_nonneg : 0 ≤ h7.c₁₁ := le_trans zero_le_one (one_le_c11 h7)

variable [DecidableEq (h7.K →+* ℂ)]

variable {z : ℂ} {l₀ : ℝ} (hz : (z : ℂ) ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq / q))))
  (hl0 : (l₀ : ℝ) < (h7.m : ℝ) * (1 + h7.r q hq0 h2mq / q))

lemma norm_hz (hz : z ∈ Metric.sphere 0 ((h7.m : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))) :
    ‖z‖ ≤ ‖(h7.m : ℝ)‖ * ‖1 + (h7.r q hq0 h2mq : ℝ) / (q: ℝ)‖ := by
  simp only [mem_sphere_iff_norm, sub_zero] at hz
  rw [hz, ← norm_mul, Real.norm_eq_abs]
  exact le_abs_self _



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
    · apply norm_sum_le
    simp only [Complex.norm_mul]
    apply Finset.sum_le_sum
    intros i hi
    simp only [norm_pos_iff, ne_eq, exp_ne_zero, not_false_eq_true, mul_le_mul_iff_left₀]
    apply norm_embedding_le_house
  · refine sum_le_sum ?_
    intro i hi
    refine mul_le_mul ?_ ?_ ?_ ?_
    · simpa using (house_eta_le_c₄_pow h7 q hq0 i h2mq)
    · simpa using (Complex.norm_exp_le_exp_norm (h7.ρ q i * z))
    · simp
    · apply mul_nonneg
      · exact Real.rpow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _
      · exact Real.rpow_nonneg (by simpa using (Nat.cast_nonneg (h7.n q))) _
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := house_eta_le_c₄_pow h7 q hq0 i h2mq
      unfold house at lemma82
      apply Preorder.le_refl _
    · unfold ρ
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
                simp only [mul_assoc]; simp_all
      · gcongr; apply norm_add_le
      · gcongr
        · simp only [RCLike.norm_natCast, _root_.norm_natCast, Nat.cast_le]
          exact ((finProdFinEquiv.symm.toFun i).1).isLt
        · simp only [Complex.norm_mul, RCLike.norm_natCast]
          apply mul_le_mul ?_ (by rfl) (by simp) (by simp)
          · simp only [Nat.cast_le]
            exact ((finProdFinEquiv.symm.toFun i).2).isLt
      · gcongr; simp
      · congr
        nth_rw 1 [← mul_one (a:=(‖(q : ℤ)‖))]
        rw [mul_add]
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [le_refl]
        · gcongr
          · exact le_abs_self (1 + ‖h7.β‖)
          · exact h7.norm_hz q hq0 h2mq hz
        · positivity
        · simp only [Int.norm_natCast, Nat.cast_nonneg]
      simp only [Real.norm_eq_abs]
      simp only [Nat.abs_cast, abs_norm, le_refl]
    · exact Real.exp_nonneg ‖h7.ρ q i * z‖
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        exact le_trans zero_le_one (h7.one_le_c₄)
      · apply Real.rpow_nonneg
        simp only [Nat.cast_nonneg]
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul (by rfl) ?_ ?_ (by positivity)
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
                simp
              · simp only [Nat.ofNat_nonneg]
          · apply Real.rpow_le_rpow_of_exponent_le
            · simp only [Nat.one_le_cast]
              trans
              · apply h7.one_le_n q hq0 h2mq
              exact n_le_r h7 q hq0 h2mq
            · refine (div_le_div_iff_of_pos_right ?_).mpr ?_
              · simp only [Nat.ofNat_pos]
              · simp only [add_le_add_iff_right, Nat.cast_le]
                exact n_le_r h7 q hq0 h2mq
        · apply Real.rpow_nonneg; simp only [Nat.cast_nonneg]
        · apply Real.rpow_nonneg; exact le_trans zero_le_one (h7.one_le_c₄)
      · rw [Real.rpow_def_of_pos (x:= h7.c₉)]
        · calc _ ≤ Real.exp ( |1 + ‖h7.β‖| *  ‖Complex.log h7.α‖ * (↑h7.m) *
                   |(q : ℝ) * (1 + ↑(h7.r q hq0 h2mq) / ↑q)|) := ?_
               _ ≤ Real.exp (Real.log h7.c₉ * (↑(h7.r q hq0 h2mq) + ↑q)) := ?_

          · simp only [Real.exp_le_exp]
            rw [norm_mul];rw [norm_mul];rw [norm_mul];rw [norm_mul]
            have : ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ *  ‖‖Complex.log h7.α‖‖ * ‖(h7.m : ℝ)‖ *
                   ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ =
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
            simp
          · simp only [mul_assoc, Real.exp_le_exp]
            have : |((h7.r q hq0 h2mq) + q : ℝ)| = (↑(h7.r q hq0 h2mq) + ↑q) := by
              simp only [abs_eq_self]; positivity
            rw [← this]
            simp only [c₉, Real.log_exp, mul_assoc]
            gcongr
            have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        · simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
            rw [this]
            rw [add_comm]
        · unfold c₉; apply Real.exp_pos
      · positivity
      · apply mul_nonneg (Real.rpow_nonneg _ _) (Real.rpow_nonneg (by positivity) _)
        exact le_trans zero_le_one (h7.one_le_c₄)
    · simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs]
      apply mul_nonneg
        (mul_nonneg (pow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _) (by positivity))
        (Real.exp_nonneg _)

def c₁₀ : ℝ := (2*h7.m* h7.c₄* h7.c₉* h7.c₉^(2*h7.m : ℝ))

lemma c10_nonneg : 0 ≤ h7.c₁₀ := by
  unfold c₁₀
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (le_trans zero_le_one (h7.one_le_c₄))) (c9_nonneg h7))
  · apply Real.rpow_nonneg; exact c9_nonneg h7

lemma one_le_c10 : 1 ≤ h7.c₁₀ := by
  unfold c₁₀
  have hm : (1 : ℝ) ≤ h7.m := by exact_mod_cast h7.one_le_m
  have h1 : (1 : ℝ) ≤ (2 : ℝ) * h7.m := by nlinarith
  have h2 : 1 ≤ (2 : ℝ) * h7.m * h7.c₄ := by
    simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h1 h7.one_le_c₄
  have h3 : 1 ≤ (2 : ℝ) * h7.m * h7.c₄ * h7.c₉ := by
    simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h2 h7.c9_gt_1
  have h4 : 1 ≤ h7.c₉ ^ (2 * h7.m : ℝ) := by
    exact Real.one_le_rpow (h7.c9_gt_1) (by positivity)
  simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h3 h4

lemma abs_R : (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq) ^
      (((h7.r q hq0 h2mq : ℝ ) + 1) / 2)) * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) ≤
      (h7.c₁₀)^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq : ℝ) ^
      (1/2 * ((h7.r q hq0 h2mq) + 3 : ℝ)) := by
    calc _ ≤ (2 * h7.m : ℝ )^(h7.r q hq0 h2mq : ℝ) *(h7.r q hq0 h2mq : ℝ)*
             ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) * (h7.r q hq0 h2mq : ℝ) ^
             (((h7.r q hq0 h2mq : ℝ) + 1) / 2)) * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_
         _ ≤ (h7.c₁₀ ^ (h7.r q hq0 h2mq : ℝ)) * (h7.r q hq0 h2mq : ℝ) ^
             (1/2 * (h7.r q hq0 h2mq + 3) : ℝ) := ?_
    · apply mul_le_mul (eq6b.extracted_1_1 h7 q hq0 h2mq) le_rfl ?_ (by positivity)
      (apply mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one h7.one_le_c₄) _)
        (by positivity)) (Real.rpow_nonneg (c9_nonneg h7) _))
    · unfold c₁₀
      nth_rw 2 [Real.mul_rpow _ (by apply Real.rpow_nonneg (c9_nonneg h7) ((2 * ↑h7.m : ℝ)))]
      · nth_rw 2 [Real.mul_rpow _ (by grind [c9_nonneg h7])]
        · nth_rw 2 [Real.mul_rpow (by positivity) (by apply le_trans zero_le_one (h7.one_le_c₄))]
          · simp only [← mul_assoc, mul_assoc ((2*h7.m : ℝ) ^ (h7.r q hq0 h2mq : ℝ))
                (h7.r q hq0 h2mq : ℝ) (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)),
                mul_comm (h7.r q hq0 h2mq : ℝ) (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ))]
            simp only [mul_assoc]; nth_rw 3 [← mul_assoc]
            apply mul_le_mul (by rfl) ?_ ?_ (by positivity)
            · apply mul_le_mul (by simp) ?_
                (mul_nonneg (by positivity) (Real.rpow_nonneg (c9_nonneg h7) _))
                (Real.rpow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _)
              · rw [Real.rpow_add (by grind [c9_pos h7]), mul_comm, mul_assoc]
                · apply mul_le_mul (by rfl) ?_ ?_ (Real.rpow_nonneg (c9_nonneg h7) _)
                  · apply mul_le_mul ?_ ?_ (by positivity)
                      (by apply Real.rpow_nonneg (Real.rpow_nonneg (c9_nonneg h7) _) _)
                    · rw [← Real.rpow_mul (c9_nonneg h7)]
                      · apply Real.rpow_le_rpow_of_exponent_le (c9_gt_1 h7)
                        · exact mod_cast le_trans (h7.q_le_two_mn q h2mq)
                           (mul_le_mul (by rfl) (n_le_r h7 q hq0 h2mq) (by positivity)
                           (by positivity))
                    · nth_rw 1 [← Real.rpow_one ((h7.r q hq0 h2mq))]
                      rw [← Real.rpow_add]
                      · exact Real.rpow_le_rpow_of_exponent_le
                          (by simp; grind [r_qt_0 h7 q hq0 h2mq]) (by ring_nf; simp)
                      · simp; grind [r_qt_0 h7 q hq0 h2mq]
                  · apply mul_nonneg (Real.rpow_nonneg (c9_nonneg h7) _) (mul_nonneg (by simp)
                      (by apply Real.rpow_nonneg (by simp)))
            · apply mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (h7.one_le_c₄)) _)
               (mul_nonneg (by positivity) (Real.rpow_nonneg (c9_nonneg h7) _))
        · apply mul_nonneg (by positivity) (le_trans zero_le_one (h7.one_le_c₄))
      · apply mul_nonneg (mul_nonneg (by positivity) (le_trans zero_le_one (h7.one_le_c₄)))
          (c9_nonneg h7)

lemma norm_sub_l0_lower_bound_on_sphere
    (hz : z ∈ Metric.sphere 0 ((h7.m : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))) :
    (h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ) ≤ ‖z - ((h7.l₀' q hq0 h2mq : ℂ) + 1)‖ := by
  calc (h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ)
    _ = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := ?_
    _ ≤ ‖z‖ - ‖(h7.l₀' q hq0 h2mq : ℂ) + 1‖ := ?_
    _ ≤ ‖z - ((h7.l₀' q hq0 h2mq : ℂ) + 1)‖ := ?_
  · ring
  · simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right]
    have : h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            - ((h7.l₀' q hq0 h2mq : ℝ) + 1) =
           h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            + (- ((h7.l₀' q hq0 h2mq : ℝ) + 1)) := rfl
    norm_cast
    simp only [Nat.cast_add, Nat.cast_one, ge_iff_le]
    rw [this, add_assoc]
    simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero]
    exact_mod_cast Fin.isLt _
  · apply norm_sub_norm_le z

include hz in
lemma norm_z_minus_km_lower_bound_on_sphere (km : Fin (h7.m)) :
  h7.m * h7.r q hq0 h2mq / q ≤ ‖z - ((km: ℂ) + 1)‖  := by
  have hz' : ‖z‖ = h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) := by
    simpa [mem_sphere_iff_norm, sub_zero] using hz
  have hkm' : (km : ℝ) ≤ h7.m := le_of_lt (by simp [Nat.cast_lt])
  have hkm : ‖(km : ℂ)‖ ≤ (h7.m : ℝ) := by simp
  calc _ = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := by ring
       _ = ‖z‖ - norm (h7.m : ℂ) := by simp [hz', sub_eq_add_neg]
       _ ≤ ‖z‖ - ‖(km : ℂ) + 1‖ := ?_
       _ ≤ ‖z - ((km : ℂ) + 1)‖ := by simp [norm_sub_norm_le z ((km : ℂ) + 1)]
  · simp only [tsub_le_iff_right]
    · rw [sub_eq_add_neg, ← tsub_le_iff_left, sub_eq_add_neg]
      simp only [neg_add_rev, neg_neg, add_neg_cancel_comm_assoc, RCLike.norm_natCast]
      exact_mod_cast Fin.isLt _

lemma prod_bound {ι} (f : ι → ℝ) (s : Finset ι) (C : ℝ) (hC : ∀ x ∈ s, 0 ≤ f x)
   (h : ∀ x ∈ s, f x ≤ C) :  ∏ x ∈ s, f x ≤ C ^ s.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod hC h

include hz h2mq in
lemma abs_denom : norm (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ))) *
  ∏ km ∈ (Finset.range (h7.m) \ {(h7.l₀' q hq0 h2mq : ℕ)}),
    (((((h7.l₀' q hq0 h2mq : ℂ) + 1 - ((km + 1 : ℂ))) / ((z - ((km + 1 : ℂ))))) ^
      (h7.r q hq0 h2mq))))
    ≤ (h7.c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
      (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := by
  let C : ℝ := (h7.m * (↑q / (↑h7.m * ↑(h7.r q hq0 h2mq)))) ^ h7.r q hq0 h2mq
  calc
    _ ≤ norm (z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ {(h7.l₀' q hq0 h2mq : ℕ)},
          (((h7.l₀' q hq0 h2mq : ℕ) + 1 - ((km : ℕ) + 1)) / (z - ((km : ℕ) + 1))) ^
            (h7.r q hq0 h2mq)) := by
          simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, add_sub_add_right_eq_sub, le_refl]
    _ ≤ (h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ {(h7.l₀' q hq0 h2mq : ℕ)},
          (((h7.l₀' q hq0 h2mq : ℕ) + 1 - ((km : ℕ) + 1)) / (z - ((km : ℕ) + 1))) ^
            (h7.r q hq0 h2mq)) := by
          apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · simp only [zpow_neg, zpow_natCast]
            refine inv_anti₀ ?_ ?_
            · refine pow_pos ?_ (h7.r q hq0 h2mq)
              refine Real.sqrt_ne_zero'.mp ?_
              refine (Real.sqrt_ne_zero (by positivity)).mpr ?_
              refine div_ne_zero ?_ ?_
              · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
                refine ⟨?_, ?_⟩
                · rw [← ne_eq]
                  exact Ne.symm (Nat.zero_ne_add_one (2 * h7.h + 1))
                · simp_rw [h7.r_ne_zero]
                  aesop
              · have : 0 < (q : ℝ) := by exact_mod_cast hq0
                exact Ne.symm (ne_of_lt this)
            · refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
                (r_ne_zero h7 q hq0 h2mq)).mpr ?_
              · grind [h7.norm_z_minus_km_lower_bound_on_sphere q hq0 h2mq hz]
          · rw [norm_prod]
    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℤ)) *
         ∏ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      (‖(((h7.l₀' q hq0 h2mq : ℕ) + 1 - ((x : ℕ) + 1)) : ℂ)‖ *
       (↑q / (↑h7.m * ↑(h7.r q hq0 h2mq)))) ^ h7.r q hq0 h2mq := by
          apply mul_le_mul
          · simp only [zpow_neg, zpow_natCast]
            rw [le_iff_eq_or_lt]
            left
            ring
          · rw [norm_prod]
            apply Finset.prod_le_prod
            · intro x hx
              rw [norm_pow, ← norm_pow]
              positivity
            · intro x hx
              simp only [norm_pow]
              rw [div_eq_mul_inv]
              refine (pow_le_pow_iff_left₀ ?_ ?_ (r_ne_zero h7 q hq0 h2mq)).mpr ?_
              · positivity
              · positivity
              · simp only [Complex.norm_mul]
                apply mul_le_mul
                · simp
                · simp only [norm_inv]
                  simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
                  let x' : Fin h7.m := ⟨x, hx.1⟩
                  have hxnorm := norm_z_minus_km_lower_bound_on_sphere h7 q hq0 h2mq hz x'
                  unfold x' at hxnorm
                  simp only at hxnorm
                  rw [← one_div_le_one_div]
                  · simp only [one_div, inv_div, div_inv_eq_mul, one_mul]
                    exact hxnorm
                  · refine div_pos ?_ ?_
                    · norm_cast
                    · apply mul_pos
                      · unfold m
                        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                        apply add_pos
                        · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                          unfold h
                          exact Module.finrank_pos
                        · simp only [Nat.ofNat_pos]
                      · simp only [Nat.cast_pos]
                        exact r_qt_0 h7 q hq0 h2mq
                  · simp only [mem_sphere_iff_norm, sub_zero] at hz
                    simp only [inv_pos]
                    calc
                      _ < ↑h7.m * ↑(h7.r q hq0 h2mq) / ↑q := by
                            apply mul_pos
                            · apply mul_pos
                              · unfold m
                                simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                                apply add_pos
                                · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                                  unfold h
                                  exact Module.finrank_pos
                                · simp only [Nat.ofNat_pos]
                              · simp only [Nat.cast_pos]
                                exact r_qt_0 h7 q hq0 h2mq
                            · simp only [inv_pos, Nat.cast_pos]
                              exact hq0
                      _ ≤ ‖z - (↑x + 1)‖ := hxnorm
                · positivity
                · positivity
          · apply norm_nonneg
          · simp only [zpow_natCast]
            apply pow_nonneg
            simp only [inv_div]
            positivity
    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℝ)) *
        C ^ Finset.card (Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}) := by
          simp only [zpow_natCast, inv_div]
          apply mul_le_mul (by simp only [Real.rpow_natCast, le_refl]) ?_ (by positivity) (by positivity)
          apply prod_bound
          · intro x hx
            positivity
          · intro x hx
            unfold C
            refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
              (r_ne_zero h7 q hq0 h2mq)).mpr ?_
            simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
            have : ‖(h7.l₀' q hq0 h2mq : ℂ) + 1 - (↑x + 1)‖ ≤ (h7.m : ℝ) := by
              simp only [add_sub_add_right_eq_sub]
              rw [← Complex.norm_natCast]
              obtain ⟨y, hy⟩ := (h7.l₀' q hq0 h2mq)
              obtain ⟨hx1, hx2⟩ := hx
              simp only [RCLike.norm_natCast]
              by_cases H : x ≤ y
              · have : ‖(y : ℂ) - (x : ℂ)‖ = ((y - x) : ℕ) := by
                  rw [← Complex.norm_natCast]
                  norm_cast
                rw [this]
                simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
                linarith
              · have : ‖(y : ℂ) - (x : ℂ)‖ = ((x - y) : ℕ) := by
                  calc
                    _ = ‖(x : ℂ) - (y : ℂ)‖ := by rw [← norm_neg]; simp only [neg_sub]
                    _ = ((x - y) : ℕ) := by
                          rw [← Complex.norm_natCast]
                          norm_cast
                          grind
                rw [this]
                simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
                linarith
            exact mul_le_mul this (le_refl _) (by positivity) (by positivity)
    _ ≤ (h7.c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
        (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := by
          simp only [inv_div, Real.rpow_natCast]
          have : #(Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}) = (h7.m - 1) := by grind
          rw [this]
          unfold C
          rw [← pow_mul]
          nth_rw 5 [mul_comm]
          rw [mul_pow, pow_mul]
          simp only [← mul_assoc]
          nth_rw 2 [mul_comm]
          simp only [mul_assoc]
          rw [← pow_add]
          unfold c₁₁
          have H1 : (h7.r q hq0 h2mq + (((h7.m : ℝ) - 1) : ℝ) * h7.r q hq0 h2mq) =
              (h7.m * h7.r q hq0 h2mq : ℝ) := by ring_nf
          apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
          simp only [← Real.rpow_natCast]
          have : ↑(h7.m - 1) = (((h7.m : ℝ) - 1) : ℝ) := Nat.cast_pred (by grind)
          simp only [Nat.cast_add, Nat.cast_mul]
          rw [this, H1]
          apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          refine (div_le_div_iff_of_pos_left (by simp only [Nat.cast_pos]; exact hq0)
            (mul_pos (by simp only [Nat.cast_pos]; exact Nat.zero_lt_succ (2 * h7.h + 1))
              (by simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq))
            (by simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq)).mpr ?_
          norm_cast
          nth_rw 1 [← one_mul (a := h7.r q hq0 h2mq)]
          exact mul_le_mul (one_le_m h7) (le_refl _) (Nat.zero_le _) (Nat.zero_le _)









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
    unfold auxiliaryRemainderRestricted
    simp only [mul_assoc]
  · nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [mul_comm  ↑(h7.r q hq0 h2mq).factorial  ‖h7.R q hq0 h2mq z‖]
    simp only [mul_assoc, zpow_neg, zpow_natCast,
    Complex.norm_mul, norm_natCast, norm_inv, norm_pow,
      norm_prod, Complex.norm_div, one_div]
  · apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · rw [mul_assoc, mul_assoc]
      · apply mul_le_mul (le_trans (h7.abs_Rb q hq0 h2mq hz) (abs_R h7 q hq0 h2mq)) ?_
            (by positivity) ?_
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

def systemCoeffsff_foo_S : ρᵣ h7 q hq0 h2mq =
  Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ)) *
   (h7.S q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1) := by
  dsimp [ρᵣ]
  congr
  have HAE : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
    intros z
    fun_prop
  let R₁ : ℂ → ℂ := analyticExtensionR h7 q hq0 h2mq ((h7.l₀' q hq0 h2mq))
  have HR1 : ∀ (z : ℂ), AnalyticAt ℂ R₁ z := by
    unfold R₁
    intros z
    apply analyticExtensionR_analyticAt h7 q hq0 h2mq (h7.l₀' q hq0 h2mq) z
  have hR₁ : ∀ (z : ℂ), (h7.R q hq0 h2mq) z =
    ((z - (h7.l₀' q hq0 h2mq + 1)) ^ (h7.r q hq0 h2mq)) * (R₁ z) := by
    intros z
    rw [h7.R_eq_pow_mul_analyticExtensionR]
  have hr : h7.r q hq0 h2mq ≤ h7.r q hq0 h2mq := by rfl
  have :
   ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧
    (∀ z, deriv^[(h7.r q hq0 h2mq)] (R h7 q hq0 h2mq) z =
   (z - ( l₀' h7 q hq0 h2mq + 1))^((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)) *
    ((h7.r q hq0 h2mq).factorial/((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)).factorial * R₁ z +
       (z - ( l₀' h7 q hq0 h2mq + 1))* R₂ z)) := by
    apply iterated_deriv_mul_pow_sub_of_analytic (z₀ := l₀' h7 q hq0 h2mq + 1)
        --HAE
        HR1 hR₁ (r := r h7 q hq0 h2mq) (k := r h7 q hq0 h2mq) hr
  simp only [tsub_self, pow_zero, Nat.factorial_zero,
  Nat.cast_one, div_one, one_mul] at this
  have := this
  obtain ⟨R2,hR⟩ := this
  clear this
  obtain ⟨hR1, hR2⟩ := hR
  rw [hR2]
  unfold R₁
  symm
  dsimp [S]
  simp only [add_left_inj, Nat.cast_inj, exists_apply_eq_apply', ↓reduceDIte]
  dsimp
  · unfold auxRemainderAtL0
    simp only [add_sub_add_right_eq_sub]
    rw [mul_comm   ↑(h7.r q hq0 h2mq).factorial
      (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1))]
    nth_rw 2 [← mul_one
      (a := (h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1)) *
      ↑(h7.r q hq0 h2mq).factorial) ]
    congr
    simp only [mul_one, sub_self, zero_mul, add_zero]
    nth_rw 2 [← mul_one (a:= h7.analyticExtensionR q hq0 h2mq (h7.l₀' q hq0 h2mq)
      ((h7.l₀' q hq0 h2mq : ℂ) + 1) * ↑(h7.r q hq0 h2mq).factorial)]
    congr
    have H1 :  ∏ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}, 1 = (1 : ℂ) := by
      simp only [prod_const_one]
    congr
    rw [← H1]
    apply Finset.prod_congr
    rfl
    intros x hx
    rw [div_self]
    simp only [one_pow]
    have : ∀ x ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
      ↑↑(h7.l₀' q hq0 h2mq) ≠ x := by
        intros x hx
        grind only [= mem_sdiff, = Finset.mem_singleton]
    have := this x hx
    intros HC
    rw [sub_eq_zero] at HC
    norm_cast at HC

lemma eq7 (l' : Fin (h7.m)) :
    ρᵣ h7 q hq0 h2mq = Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq) : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq / q))), (z - (h7.l₀' q hq0 h2mq + 1))⁻¹ *
    (h7.S q hq0 h2mq) z)) :=
  h7.hcauchy q hq0 h2mq ▸ systemCoeffsff_foo_S h7 q hq0 h2mq

def c₁₃ : ℝ :=((‖Complex.log h7.α‖⁻¹ + 1)*h7.m*(2 + 1/h7.m)*h7.c₁₂)

lemma c13_nonneg : 0 ≤ h7.c₁₃ := by
  unfold c₁₃
  apply mul_nonneg (by positivity) (h7.c12_nonneg)

lemma one_le_c13 : 1 ≤ h7.c₁₃ := by
  unfold c₁₃
  refine one_le_mul_of_one_le_of_one_le ?_ (h7.one_le_c12)
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · rw [add_comm]
      refine le_add_of_le_of_nonneg (le_refl _) (by positivity)
    · simp only [Nat.one_le_cast]; exact Nat.le_of_ble_eq_true rfl
  · simp only [one_div]
    refine le_add_of_le_of_nonneg (by aesop) (by positivity)

def Cnum : ℝ := ((h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ))⁻¹ * (h7.c₁₂ ^ (h7.r q hq0 h2mq : ℝ)*
  (h7.r q hq0 h2mq : ℝ) ^ ((((h7.r q hq0 h2mq : ℝ)* (((3 : ℝ) - h7.m) / 2 : ℝ)) + (3 / 2 : ℝ))))

lemma hf : ∀ z ∈ Metric.sphere 0 (h7.m * (1 + ↑(h7.r q hq0 h2mq : ℝ) / ↑q)),
    ‖(z - ((↑(h7.l₀' q hq0 h2mq) : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)‖ ≤ h7.Cnum q hq0 h2mq := by
  intros z hz
  simp only [Complex.norm_mul, norm_inv, Cnum]
  apply mul_le_mul ?_ (S_norm_bound h7 q hq0 h2mq hz) (by positivity) (by positivity)
  · apply inv_anti₀ ?_ (h7.norm_sub_l0_lower_bound_on_sphere q hq0 h2mq hz)
    · refine Real.sqrt_ne_zero'.mp ?_
      · refine (Real.sqrt_ne_zero (by positivity)).mpr ?_
        refine div_ne_zero ?_ (Ne.symm (ne_of_lt (mod_cast hq0)))
        · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
          refine ⟨by simp [m], by simp_rw [h7.r_ne_zero]; simp only [not_false_eq_true]⟩

lemma eq8 :
    norm (ρᵣ h7 q hq0 h2mq) ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
    ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) * ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := by

  have hR : 0 ≤ (h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q) : ℝ) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply add_nonneg zero_le_one
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

  have H := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
    (h7.hf q hq0 h2mq)

  calc _ = norm (Complex.log h7.α ^ (-(h7.r q hq0 h2mq : ℤ)) * ((2 * Real.pi) * I)⁻¹ * ∮ (z : ℂ) in
           C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)), (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ *
           (h7.S q hq0 h2mq z)) := ?_

       _ = norm (Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ))) *
           norm ((2 * Real.pi * I)⁻¹) * norm (∮ (z : ℂ) in
           C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
           (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)) := ?_

       _ ≤ ((norm ((Complex.log h7.α))^ (-(h7.r q hq0 h2mq : ℤ)))) * (h7.m : ℝ) *
           (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) * (h7.c₁₂) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) * (3 - h7.m : ℝ) / 2 + 3 / 2) *
           ((q : ℝ) / (((h7.m : ℝ) * (h7.r q hq0 h2mq : ℝ))))) := ?_

       _ ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) * ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := ?_

  · rw [h7.eq7 q hq0 h2mq]
    · simp only [mul_assoc]
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
        · apply H
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
lemma use6and8 : norm ((Algebra.norm ℚ (rho h7 q hq0 h2mq))) ≤ (h7.c₁₄)^(h7.r q hq0 h2mq : ℝ) *
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
    · apply eq8 h7 q hq0 h2mq
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
    have : ((h7.h : ℝ) - 1) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
    ((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ)) / 2 + 3 / 2) =
    (-(h7.r q hq0 h2mq : ℝ)) / 2 + 3 * (h7.h) / 2 := by
     unfold m
     push_cast
     ring
    rw [← this]
    unfold m
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

def c₁₅ : ℝ := h7.c₁₄ * h7.c₅

lemma c15_nonneg : 0 ≤ h7.c₁₅ := by
  unfold c₁₅; exact mul_nonneg (zero_le_one.trans h7.c14_nonneg) (c5nonneg h7).le

lemma c15_geg_1 : 1 ≤ h7.c₁₅ := by
  unfold c₁₅ c₅
  exact one_le_mul_of_one_le_of_one_le h7.c14_nonneg (one_le_pow₀ (by simp))

theorem norm_pos_rho : 0 < ‖(Algebra.norm ℚ) (h7.rho q hq0 h2mq)‖ := by
  rw [norm_pos_iff, ne_eq, Algebra.norm_eq_zero_iff]
  rintro H
  apply ρᵣ_nonzero h7 q hq0 h2mq
  simpa [← rho_eq_ρᵣ]

lemma norm_algebraNorm_rho_gtinv :
    norm ((Algebra.norm ℚ) (h7.rho q hq0 h2mq)) ⁻¹ < h7.c₅ ^ ((h7.r q hq0 h2mq : ℝ)) := by
  have h := norm_algebraNorm_rho_gt h7 q hq0 h2mq
  rw [← inv_lt_inv₀] at h
  · simpa [← Real.rpow_neg] using h
  · exact norm_pos_rho h7 q hq0 h2mq
  · simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pos]
    apply pow_pos (c5nonneg h7)

include u t in
lemma use5 : (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2) <
  (h7.c₁₅) ^ (h7.r q hq0 h2mq : ℝ) := by
  let r : ℝ := h7.r q hq0 h2mq
  let N : ℝ := ‖(Algebra.norm ℚ) (h7.rho q hq0 h2mq)‖
  let B : ℝ := r ^ (-r / 2 + 3 * h7.h / 2)

  have hrpos : 0 < r := by
    dsimp [r]
    exact_mod_cast r_qt_0 h7 q hq0 h2mq
  have hNpos : 0 < N := by
    simpa [N] using norm_pos_rho h7 q hq0 h2mq
  have hBpos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos hrpos _

  have h68 : N ≤ h7.c₁₄ ^ r * B := by
    dsimp [N, r, B]
    simpa using (use6and8 h7 q hq0 u t h2mq)

  have htmp :
        N * B⁻¹ ≤ (h7.c₁₄ ^ r * B) * B⁻¹ :=
      mul_le_mul_of_nonneg_right h68 (inv_nonneg.mpr (le_of_lt hBpos))

  have h1 : N * B⁻¹ ≤ h7.c₁₄ ^ r := by
    simpa [mul_assoc, mul_inv_cancel₀ hBpos.ne', mul_one] using htmp

  have hle : B⁻¹ ≤ N⁻¹ * (h7.c₁₄ ^ r) := by
    have htmp :
        N⁻¹ * (N * B⁻¹) ≤ N⁻¹ * (h7.c₁₄ ^ r) :=by
      apply mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt hNpos))
    grind [mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

  have hltN : N⁻¹ < h7.c₅ ^ r := by
    dsimp [N, r]
    simpa using (norm_algebraNorm_rho_gtinv h7 q hq0 h2mq)

  have hApos : 0 < h7.c₁₄ ^ r := by
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one h7.c14_nonneg) _

  have hmulrpow : (h7.c₁₅) ^ r = (h7.c₁₄ ^ r) * (h7.c₅ ^ r) := by
    unfold c₁₅
    rw [Real.mul_rpow (le_trans zero_le_one h7.c14_nonneg) (c5nonneg h7).le]

  calc
    (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2)
        = B⁻¹ := by
            dsimp [B, r]
            rw [show (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2) =
                - (-(h7.r q hq0 h2mq : ℝ) / 2 + 3 * h7.h / 2) by ring]
            rw [Real.rpow_neg (le_of_lt (by
              exact_mod_cast r_qt_0 h7 q hq0 h2mq))]
    _ ≤ N⁻¹ * (h7.c₁₄ ^ r) := hle
    _ = (h7.c₁₄ ^ r) * N⁻¹ := by ring
    _ < (h7.c₁₄ ^ r) * (h7.c₅ ^ r) := mul_lt_mul_of_pos_left hltN hApos
    _ = (h7.c₁₅) ^ r := hmulrpow.symm
    _ = (h7.c₁₅) ^ (h7.r q hq0 h2mq : ℝ) := by rfl

end Setup


end
