/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainPostAnalytic

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
  (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup

/-! On the other hand `house (ρ) ≤ t c₄ⁿ n⁽ⁿ⁻¹⁾⁄₂ (c₆q)ʳ c₇^q ≤ c₈ʳ r⁽ʳ⁺³⁾⁄₂`.
-/

lemma one_le_c₄ : 1 ≤ h7.c₄ := one_le_mul_of_one_le_of_one_le
  (le_max_left 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m))) (h7.one_le_c₃)

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

omit [DecidableEq (h7.K →+* ℂ)] in
lemma one_le_c₇ : 1 ≤ h7.c₇ := by
  unfold c₇
  have hc : 0 ≤ h7.c₁ := le_trans Int.one_nonneg h7.one_le_c₁
  have house_num_mul_int (α : h7.K) (c' : ℤ) (hc' : 0 ≤ c') :
      house ((c' : h7.K) * α) = |(c' : ℝ)| * house α := by
    lift c' to ℕ using hc'
    simpa using house_nat_mul α c'
  have hα : 1 ≤ |(h7.c₁ : ℝ)| * house h7.α' := by
    rw [← house_num_mul_int (α := h7.α') (c' := h7.c₁) hc, ← smul_eq_mul]
    exact one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁α) (mod_cast h7.c₁α_ne_zero)
  have hγ : 1 ≤ |(h7.c₁ : ℝ)| * house h7.γ' := by
    rw [← house_num_mul_int (α := h7.γ') (c' := h7.c₁) hc, ← smul_eq_mul]
    exact one_le_house_of_isIntegral (mod_cast h7.isIntegral_c₁γ) (mod_cast h7.c₁γ_ne_zero)
  have hbase :
      1 ≤ |(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)| *
        (|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| * house h7.γ'))) := by
    calc
      1 ≤ (|(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)|) *
            ((|(h7.c₁ : ℝ)| * house h7.α') * (|(h7.c₁ : ℝ)| * house h7.γ')) := by
          refine one_le_mul_of_one_le_of_one_le
            (one_le_mul_of_one_le_of_one_le
              (by
                norm_cast
                exact one_le_abs_c₁ h7)
              (by
                norm_cast
                exact one_le_abs_c₁ h7))
            (one_le_mul_of_one_le_of_one_le hα hγ)
      _ = |(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)| *
            (|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| * house h7.γ'))) := by
          ring
  calc
    (1 : ℝ) = 1 ^ h7.m := by simp
    _ ≤ (|(h7.c₁ : ℝ)| * |(h7.c₁ : ℝ)| *
          (|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| * house h7.γ')))) ^ h7.m := by
        refine pow_le_pow_left₀ (by positivity) hbase h7.m

lemma r_qt_0 : 0 < h7.r q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (h7.r_ne_zero q hq0 h2mq)

lemma one_le_r : 1 ≤  h7.r q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (h7.r_ne_zero q hq0 h2mq)

lemma cρ_abs_eq : |h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q)| =
  h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q) := by
    rw [abs_eq_self]
    apply mul_nonneg (pow_nonneg (le_trans Int.one_nonneg h7.one_le_c₁) _)
    · apply pow_nonneg (le_trans Int.one_nonneg h7.one_le_c₁)

lemma eq6a : house (rho h7 q hq0 h2mq) ≤
  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := by
  calc _ ≤ norm (h7.cρ q hq0 h2mq : ℝ) * house (rho h7 q hq0 h2mq) := ?_
       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ))  *
          house (∑ t, ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
        ((h7.systemCoeffs_r q hq0 t h2mq)))) := ?_
       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ)) *
         ∑ t, house ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
       ((h7.systemCoeffs_r q hq0 t h2mq))) := ?_
       _ = (∑ t, house ((h7.cρ q hq0 h2mq) *
         (algebraMap (𝓞 h7.K) h7.K ((h7.η q hq0 h2mq) t) *
          h7.systemCoeffs_r q hq0 t h2mq))) := ?_
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
        * h7.systemCoeffs_r q hq0 i h2mq
    · exact
      house_nonneg (∑ t, (algebraMap (𝓞 h7.K) h7.K)
        (h7.η q hq0 h2mq t) * h7.systemCoeffs_r q hq0 t h2mq)
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
    (h7.η q hq0 h2mq i) * h7.systemCoeffs_r q hq0 i h2mq))]
    · simp only [Real.norm_eq_abs]
    · exact zero_le_c1rho h7 q hq0 h2mq
  · apply Finset.sum_congr rfl
    intros t ht
    rw [Algebra.left_comm (↑(h7.cρ q hq0 h2mq))
      (h7.η q hq0 h2mq t) (h7.systemCoeffs_r q hq0 t h2mq)]
    simp only [← zsmul_eq_mul]
    unfold systemCoeffs_r
    unfold cρ
    rw [cρ_abs_eq]
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
  · refine Finset.sum_le_sum ?_
    intro t ht
    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg ?_ ?_ (house_nonneg _) (by positivity)
    · simp [nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, Int.cast_pow]
    · trans
      · exact house_mul_le _ _
      ·
        refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity) <;>
          simp [house]
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · apply h7.house_eta_le_c₄_pow q hq0 t h2mq
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
                apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (zero_le _) (zero_le _)
                · exact (h7.l₀' q hq0 h2mq).isLt
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              · apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁γ
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁γ_ne_zero
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (zero_le _) (zero_le _)
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
        · exact le_trans zero_le_one (h7.one_le_c₄)
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
        · exact le_trans zero_le_one (h7.one_le_c₄)
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
          · exact le_trans zero_le_one (h7.one_le_c₄)
        · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact le_trans zero_le_one (h7.one_le_c₄)
        · positivity
      · unfold house; positivity
    · positivity

theorem bound_n_le_r' : ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
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
      exact le_trans zero_le_one (h7.one_le_c₄)

lemma q_le_2sqrtmr : q^2 ≤ 2*h7.m*h7.r q hq0 h2mq := by
  trans
  · apply h7.q_sq_le_two_mn q h2mq
  refine Nat.mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq)

lemma sqt_etc : Real.sqrt (2*h7.m*(h7.r q hq0 h2mq)) =
  Real.sqrt (2*h7.m) * (h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ) := by
    rw [Real.sqrt_mul]
    · congr
      exact Real.sqrt_eq_rpow ↑(h7.r q hq0 h2mq)
    · positivity

def c₈ : ℝ := (h7.c₆ * √(2 * ↑h7.m) * h7.c₇ ^ (2 * h7.m) * h7.c₄ * (2 * ↑h7.m))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c7_nonneg : 0 ≤ h7.c₇ := by
  unfold c₇ house
  positivity

lemma c8_nonneg : 0 ≤ h7.c₈ := by
  unfold c₈
  apply mul_nonneg ?_ (by positivity)
  · apply mul_nonneg ?_ (le_trans zero_le_one (h7.one_le_c₄))
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

theorem q_sq2_neq_1 (m q : ℕ) (_ : 0 < q)
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
    · norm_cast; exact h7.q_sq_le_two_mn q h2mq
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
    · norm_cast; exact h7.q_sq_le_two_mn q h2mq
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

open Real

include h2mq in
lemma q_eq_sqrtmn : q = sqrt (2 * h7.m* h7.n q) := by
  norm_cast
  rw [← h7.q_sq_eq_two_mn q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, sqrt_sq]

set_option linter.style.multiGoal false in
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
  · -- keep your existing first block unchanged
    apply mul_le_mul (eq6b.extracted_1_1 h7 q hq0 h2mq)
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
              · have := h7.q_eq_sqrtmn q h2mq
                calc _ ≤ √(2 * ↑h7.m) * ↑(h7.n q) ^ (1 / 2 : ℝ) := ?_
                     _ ≤ √(2 * ↑h7.m) * ↑(h7.r q hq0 h2mq) ^ (1 / 2 : ℝ) := ?_
                · rw [this]
                  rw [Real.sqrt_mul]
                  refine mul_le_mul_of_nonneg_left ?_ ?_
                  · rw [le_iff_lt_or_eq]
                    right
                    exact Real.sqrt_eq_rpow ↑(h7.n q)
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg]
                  grind
                · refine mul_le_mul_of_nonneg_left ?_ ?_
                  · apply Real.rpow_le_rpow
                    · simp only [Nat.cast_nonneg]
                    · simp only [Nat.cast_le]
                      exact n_le_r h7 q hq0 h2mq
                    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg]
              · unfold c₆ house; positivity
          · simp only [Real.rpow_natCast]
            rw [← pow_mul]
            refine pow_le_pow_right₀ ?_ ?_
            · exact one_le_c₇ h7
            · trans
              · apply h7.q_le_two_mn q h2mq
              apply mul_le_mul (le_refl _) (n_le_r h7 q hq0 h2mq)
                (by positivity) (by positivity)
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
                exact le_trans zero_le_one (h7.one_le_c₄)
              · positivity
          · positivity
        · positivity
    · positivity
  · -- keep your existing second block unchanged
    nth_rw 2 [Real.mul_rpow]
    nth_rw 4 [mul_comm]
    nth_rw 2 [mul_assoc]
    simp only [← mul_assoc]
    nth_rw 3 [mul_assoc]
    nth_rw 1 [← mul_comm]
    rw [mul_comm ((2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ)) (h7.r q hq0 h2mq : ℝ)]
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
      · exact le_trans zero_le_one (h7.one_le_c₄)
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
      · exact le_trans zero_le_one (h7.one_le_c₄)
    · apply pow_nonneg
      · exact c7_nonneg h7
    · exact le_trans zero_le_one (h7.one_le_c₄)
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
  · apply h7.eq6a q hq0 h2mq
  exact h7.eq6b q hq0 h2mq


end Setup

end
