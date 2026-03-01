/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainBounds

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
  (t : Fin (q * q)) (h2mq : 2 * h7.m ∣ q ^ 2) [DecidableEq (h7.K →+* ℂ)]

namespace Setup

/-- The Gelfond-Schneider Theorem (Hilbert's Seventh Problem). -/
theorem transcendental_cpow_of_isAlgebraic_of_irrational (α β : ℂ)
    (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (htriv : α ≠ 0 ∧ α ≠ 1) (hirr : ∀ i j : ℤ, β ≠ i / j) :
    Transcendental ℚ (α ^ β) := fun hγ => by

  obtain ⟨K, hK, hNK, σ, hd, α', β', γ', habc⟩ :=
    exists_common_field_of_isAlgebraic α β (α^β) hα hβ hγ
  have h7 : Setup :=
    Setup.mk α β K σ α' β' γ' hirr htriv hα hβ habc hd
  haveI : DecidableEq (h7.K →+* ℂ) := h7.hd
  let q : ℕ := 2 * h7.m * ((6 * h7.h) * Nat.ceil (h7.c₁₅ ^ 4))
  have hq0 : 0 < q := by
    simp only [q, CanonicallyOrderedAdd.mul_pos, Nat.ofNat_pos, Nat.ceil_pos,true_and]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), ?_⟩
    refine ⟨Module.finrank_pos, ?_⟩
    · apply pow_pos
      grind [h7.c15_geg_1]

  have h2mq : 2 * h7.m ∣ q ^ 2 := by
    rw [pow_two, mul_assoc]; exact dvd_mul_right _ _

  let u : Fin (h7.m * h7.n q) := ⟨0, by
    apply mul_pos (Nat.zero_lt_succ (2 * h7.h + 1));
    apply Nat.div_pos (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq) ?_
    · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      exact Nat.zero_lt_succ (2 * h7.h + 1)⟩

  let t : Fin (q * q) := ⟨0, mul_pos hq0 hq0⟩

  -- have hnr : (h7.n q : ℝ) ≤ (h7.r q hq0 h2mq : ℝ) :=
  --   mod_cast n_le_r h7 q hq0 h2mq

  have H1 : (2 * h7.m) * (6 * h7.h) ≤ q := by
    unfold q
    apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · nth_rw 1 [← mul_one (a := 6* h7.h)]
      apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
      · simp only [Nat.one_le_ceil_iff];
        apply pow_pos
        grind [h7.c15_geg_1]

  have H2 : (2 * h7.m) * h7.c₁₅ ^ 4 ≤ q := by
    simp only [q, mul_assoc, Nat.cast_mul, Nat.cast_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀]
    apply mul_le_mul (le_refl _) ?_ ?_ (by positivity)
    · nth_rw 1 [← one_mul (a := (h7.c₁₅ ^ 4) )]
      nth_rw 1 [← mul_assoc]
      apply mul_le_mul ?_ (Nat.le_ceil (h7.c₁₅ ^ 4)) (by positivity) (by positivity)
      · unfold h;
        refine one_le_mul_of_one_le_of_one_le (Nat.one_le_ofNat) ?_
        · norm_cast
          grind [Module.finrank_pos]
    · apply pow_nonneg
      grind [h7.c15_geg_1]

  have H3 : 6* h7.h ≤ h7.n q := by
    unfold n
    calc _ ≤ ((2 * h7.m) * (6 * h7.h)) ^ 2 / (2 * h7.m) := ?_
         _ ≤  h7.n q := ?_
    · refine (Nat.le_div_iff_mul_le ?_).mpr ?_
      · have : 0 < h7.h := by grind [Module.finrank_pos]
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
        grind [Module.finrank_pos]
      apply mul_pos (by aesop) (Nat.zero_lt_succ (2 * h7.h + 1))
    · rw [mul_comm, mul_pow]
      apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
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

  have H5 : 6* h7.h ≤ h7.r q hq0 h2mq := H3.trans (n_le_r h7 q hq0 h2mq)

  have H6 : (h7.c₁₅)^4 ≤ h7.r q hq0 h2mq := by
    trans
    · apply H4
    simp only [Nat.cast_le]
    exact n_le_r h7 q hq0 h2mq

  apply absurd (use5 h7 q hq0 u t h2mq) ?_
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
                grind [Module.finrank_pos]
              simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, Nat.cast_pos, gt_iff_lt]
              grind
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
    · apply div_ne_zero
      · have : 3 * h7.h < (h7.r q hq0 h2mq : ℝ) := by
          calc _ < (6 * h7.h : ℝ)  := by norm_cast; grind [Module.finrank_pos]
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

/-!
A formalization of a proof that `√2 ^ √2` is transcendental.
-/
lemma sqrt2sqrt_is_transcendental : Transcendental ℚ ((√2 : ℂ)^ (√2 : ℂ)) := by
  apply Setup.transcendental_cpow_of_isAlgebraic_of_irrational √2 √2
  · refine IsAlgebraic.of_aeval ?_ (fun H ↦ ?_) ?_ ?_
    · exact Polynomial.X ^ 2 - Polynomial.C 1
    · have : ((((Polynomial.X ^ 2 - Polynomial.C 1) : ℚ[X])).natDegree : ℕ) = 2 := by {
        refine (degree_eq_iff_natDegree_eq_of_pos ?_).mp ?_
        · simp only [Nat.ofNat_pos]
        · rw [Polynomial.degree_sub_C]
          · simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
      }
      have HC : 2 ≠ 0 := by {simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]}
      apply HC
      rw [← this, ← H]
    · simp only [map_one, Nat.ofNat_pos, leadingCoeff_X_pow_sub_one,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [map_one, map_sub, map_pow, aeval_X]
      norm_cast
      rw [Real.sq_sqrt (x:=2)]
      · ring_nf
        exact isAlgebraic_one
      · positivity
  · refine IsAlgebraic.of_aeval ?_ (fun H ↦ ?_) ?_ ?_
    · exact Polynomial.X ^ 2 - Polynomial.C 1
    · have : ((((Polynomial.X ^ 2 - Polynomial.C 1) : ℚ[X])).natDegree : ℕ) = 2 := by {
        refine (degree_eq_iff_natDegree_eq_of_pos ?_).mp ?_
        · simp only [Nat.ofNat_pos]
        · rw [Polynomial.degree_sub_C]
          · simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
      }
      have HC : 2 ≠ 0 := by {simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]}
      apply HC
      rw [← this, ← H]
    · simp only [map_one, Nat.ofNat_pos, leadingCoeff_X_pow_sub_one,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [map_one, map_sub, map_pow, aeval_X]
      norm_cast
      rw [Real.sq_sqrt (x:=2)]
      · ring_nf
        exact isAlgebraic_one
      · positivity
  · simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, ofReal_eq_one, Real.sqrt_eq_one, OfNat.ofNat_ne_one, and_self]
  · have :=  irrational_sqrt_two
    unfold Irrational at this
    simp only [Set.mem_range, not_exists] at this
    intros i j
    let x : ℚ := (i : ℚ)/ (j : ℚ)
    intros H
    have := this x
    unfold x at this
    apply this
    symm
    norm_num
    norm_cast at H
    rw [H]
    simp_all only [Rat.cast_inj, forall_eq]

end
