/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Laura Capuano, Amos Turchet
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval

/-!
# Siegel's Lemma

In this file we introduce and prove Siegel's Lemma in its most basic version. This is a fundamental
tool in diophantine approximation and transcendence and says that there exists a "small" integral
non-zero solution of a non-trivial underdetermined system of linear equations with integer
coefficients.

## Main results

- `ThueSiegel.exists_int_vec_abs_le_of_pow_lt`: the *inequality* form, in which the linear forms
  have arbitrary real coefficients and one only asks that they take small values.
- `exists_ne_zero_int_vec_norm_le`: Given a non-zero `m × n` matrix `A` with `m < n` the linear
  system it determines has a non-zero integer solution `t` with
  `‖t‖ ≤ ((n * ‖A‖) ^ ((m : ℝ) / (n - m)))`

## Notation

- `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
  the entries of the matrix

## References

See [M. Hindry and J. Silverman, Diophantine Geometry: an Introduction][hindrysilverman00].
-/

public section

/- We set ‖⬝‖ to be Matrix.seminormedAddCommGroup  -/
attribute [local instance] Matrix.seminormedAddCommGroup

open Matrix Finset

namespace Int.Matrix

variable {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)

-- Some definitions and relative properties

local notation3 "m" => Fintype.card α
local notation3 "n" => Fintype.card β
local notation3 "e" => m / ((n : ℝ) - m) -- exponent
local notation3 "B" => Nat.floor (((n : ℝ) * max 1 ‖A‖) ^ e)
-- B' is the vector with all components = B
local notation3 "B'" => fun _ : β => (B : ℤ)
-- T is the box [0 B]^n
local notation3 "T" => Finset.Icc 0 B'
local notation3 "P" => fun i : α => ∑ j : β, B * posPart (A i j)
local notation3 "N" => fun i : α => ∑ j : β, B * (-negPart (A i j))
-- S is the box where the image of T goes
local notation3 "S" => Finset.Icc N P

section preparation

/- In order to apply Pigeonhole we need:
# Step 1: ∀ v ∈  T, A *ᵥ v ∈  S
and
# Step 2: #S < #T
Pigeonhole will give different x and y in T with A.mulVec x = A.mulVec y in S
Their difference is the solution we are looking for.
-/

-- # Step 1: ∀ v ∈ T, A *ᵥ v ∈  S

private lemma image_T_subset_S [DecidableEq α] [DecidableEq β] (v) (hv : v ∈ T) : A *ᵥ v ∈ S := by
  rw [mem_Icc] at hv ⊢
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  all_goals
    simp only [mulVec_apply_eq_sum, mul_neg]
    gcongr ∑ _ : β, ?_ with j _ -- Get rid of sums
    conv in A i j * v j => rw [← posPart_sub_negPart (A i j)]
    linarith [mul_nonneg (hv.1 j) (posPart_nonneg (A i j)),
      mul_nonneg (hv.1 j) (negPart_nonneg (A i j)),
      mul_nonneg (sub_nonneg.mpr (hv.2 j)) (posPart_nonneg (A i j)),
      mul_nonneg (sub_nonneg.mpr (hv.2 j)) (negPart_nonneg (A i j))]

-- # Preparation for Step 2

private lemma card_T_eq [DecidableEq β] : #T = (B + 1) ^ n := by
  simp [Pi.card_Icc]

-- This lemma is necessary to be able to apply the formula #(Icc a b) = b + 1 - a
private lemma N_le_P_add_one (i : α) : N i ≤ P i + 1 := by
  calc
    N i ≤ 0 := by
      simpa using sum_nonneg fun _ _ ↦ by positivity
    _ ≤ P i + 1 :=
      add_nonneg (sum_nonneg fun _ _ ↦ by positivity) zero_le_one

private lemma card_S_eq [DecidableEq α] : #(Finset.Icc N P) = ∏ i : α, (P i - N i + 1) := by
  rw [Pi.card_Icc N P, Nat.cast_prod]
  congr with i
  rw [Int.card_Icc_of_le (N i) (P i) (N_le_P_add_one A i)]
  exact add_sub_right_comm (P i) 1 (N i)

/-- The sup norm of a non-zero integer matrix is at least one. -/
lemma one_le_norm_A_of_ne_zero (hA : A ≠ 0) : 1 ≤ ‖A‖ := by
  obtain ⟨i, j, hij⟩ := (Function.ne_iff.mp hA).imp fun _ hi ↦ Function.ne_iff.mp hi
  calc
    1 ≤ ‖A i j‖ := by
      rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
      exact Int.one_le_abs hij
    _ ≤ ‖A‖ := norm_entry_le_entrywise_sup_norm A

-- # Step 2: #S < #T

open Real Nat

private lemma card_S_lt_card_T [DecidableEq α] [DecidableEq β]
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    #S < #T := by
  zify -- This is necessary to use card_S_eq
  rw [card_T_eq A, card_S_eq]
  rify -- This is necessary because ‖A‖ is a real number
  calc
  ∏ x : α, (∑ x_1 : β, ↑B * ↑(A x x_1)⁺ - ∑ x_1 : β, ↑B * -↑(A x x_1)⁻ + 1)
    ≤ ∏ x : α, (n * max 1 ‖A‖ * B + 1) := by
      refine Finset.prod_le_prod₀ (fun i _ ↦ ?_) (fun i _ ↦ ?_)
      · have h := N_le_P_add_one A i
        rify at h
        linarith only [h]
      · simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, add_le_add_iff_right]
        have h1 : n * max 1 ‖A‖ * B = ∑ _ : β, max 1 ‖A‖ * B := by
          simp [mul_assoc]
        simp_rw [h1, ← Finset.sum_add_distrib, ← mul_add, mul_comm (max 1 ‖A‖), ← Int.cast_add]
        gcongr with j _
        rw [posPart_add_negPart (A i j), Int.cast_abs]
        exact le_trans (norm_entry_le_entrywise_sup_norm A) (le_max_right ..)
  _ = (n * max 1 ‖A‖ * B + 1) ^ m := by simp
  _ ≤ (n * max 1 ‖A‖) ^ m * (B + 1) ^ m := by
        rw [← mul_pow, mul_add, mul_one]
        gcongr
        exact one_le_mul_of_one_le_of_one_le (mod_cast hm.trans hn) <| le_max_left ..
  _ = ((n * max 1 ‖A‖) ^ (m / ((n : ℝ) - m))) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        congr 1
        rw [← rpow_mul (by positivity), ← Real.rpow_natCast, div_mul_cancel₀]
        exact sub_ne_zero_of_ne (mod_cast hn.ne')
  _ < (B + 1) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        gcongr
        · exact sub_pos.mpr (mod_cast hn)
        · exact Nat.lt_floor_add_one _
  _ = (B + 1) ^ n := by
        rw [← rpow_natCast, ← rpow_add (Nat.cast_add_one_pos B), ← rpow_natCast, sub_add_cancel]

end preparation

theorem exists_ne_zero_int_vec_norm_le
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) : ∃ t : β → ℤ, t ≠ 0 ∧
    A *ᵥ t = 0 ∧ ‖t‖ ≤ (n * max 1 ‖A‖) ^ ((m : ℝ) / (n - m)) := by
  classical
  -- Pigeonhole
  rcases exists_ne_map_eq_of_card_lt_of_maps_to (card_S_lt_card_T A hn hm) (image_T_subset_S A)
    with ⟨x, hxT, y, hyT, hneq, hfeq⟩
  -- Proofs that x - y ≠ 0 and x - y is a solution
  refine ⟨x - y, sub_ne_zero.mpr hneq, by simp [mulVec_sub, hfeq], ?_⟩
  -- Inequality
  have n_mul_norm_A_pow_e_nonneg : 0 ≤ (n * max 1 ‖A‖) ^ e := by positivity
  rw [← norm_replicateCol (ι := Unit), norm_le_iff n_mul_norm_A_pow_e_nonneg]
  intro i j
  simp only [replicateCol_apply, Pi.sub_apply, Int.norm_eq_abs, ← Int.cast_abs]
  calc
    ((|x i - y i| : ℤ) : ℝ) ≤ ((B : ℤ) : ℝ) := by
      rw [Int.cast_le, abs_le]
      rw [Finset.mem_Icc] at hxT hyT
      have : 0 ≤ x i ∧ x i ≤ B ∧ 0 ≤ y i ∧ y i ≤ B := ⟨hxT.1 i, hxT.2 i, hyT.1 i, hyT.2 i⟩
      lia
    _ ≤ _ := by simpa only [Int.cast_natCast] using Nat.floor_le n_mul_norm_A_pow_e_nonneg

theorem exists_ne_zero_int_vec_norm_le'
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) (hA : A ≠ 0) :
    ∃ t : β → ℤ, t ≠ 0 ∧
    A *ᵥ t = 0 ∧ ‖t‖ ≤ (n * ‖A‖) ^ ((m : ℝ) / (n - m)) := by
  simpa [max_eq_right (one_le_norm_A_of_ne_zero A hA)] using
    exists_ne_zero_int_vec_norm_le A hn hm

end Int.Matrix

/-!
### The inequality form

The version above produces an exact solution of an integral linear system.  The following
variant allows arbitrary real coefficients and only asks the linear forms to be small; it is
the form used to construct auxiliary functions in transcendence proofs.
-/

namespace ThueSiegel

variable {ν μ : ℕ}


/-- If two points of `[0, l * c]` have the same index among the `l` boxes of length `c`
(the last box being closed at the top), they are at distance at most `c`. -/
private lemma mem_box {c : ℝ} (hc : 0 < c) {l : ℕ} (hl : 0 < l) {x : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ l * c) :
    ((min (l - 1) ⌊x / c⌋.toNat : ℕ) : ℝ) * c ≤ x ∧
      x ≤ (((min (l - 1) ⌊x / c⌋.toNat : ℕ) : ℝ) + 1) * c := by
  set q : ℝ := x / c with hqdef
  have hq0 : 0 ≤ q := div_nonneg hx hc.le
  have hxq : x = q * c := by rw [hqdef]; field_simp
  set n : ℕ := ⌊q⌋.toNat with hndef
  have hnn : (0 : ℤ) ≤ ⌊q⌋ := Int.floor_nonneg.2 hq0
  have hncast : ((n : ℕ) : ℝ) = (⌊q⌋ : ℝ) := by
    rw [hndef]; exact_mod_cast Int.toNat_of_nonneg hnn
  have hn : ((n : ℕ) : ℝ) ≤ q := by rw [hncast]; exact Int.floor_le q
  have hn' : q ≤ ((n : ℕ) : ℝ) + 1 := by rw [hncast]; exact (Int.lt_floor_add_one q).le
  rcases le_or_gt n (l - 1) with h | h
  · rw [min_eq_right h]
    exact ⟨by rw [hxq]; exact mul_le_mul_of_nonneg_right hn hc.le,
      by rw [hxq]; exact mul_le_mul_of_nonneg_right hn' hc.le⟩
  · have hlq : ((l : ℕ) : ℝ) ≤ q :=
      le_trans (by exact_mod_cast (by omega : (l : ℕ) ≤ n)) hn
    have hxl : x = (l : ℝ) * c :=
      le_antisymm hx' (by rw [hxq]; exact mul_le_mul_of_nonneg_right hlq hc.le)
    rw [min_eq_left (by omega)]
    have hl1 : (((l - 1 : ℕ) : ℝ)) + 1 = (l : ℝ) := by
      rw [Nat.cast_sub hl]; push_cast; ring
    refine ⟨?_, by rw [hxl, hl1]⟩
    rw [hxl]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le l 1) hc.le

/-- **Thue–Siegel's lemma**, inequality form (Lemma 4.11 of [waldschmidt2000]).

If the `μ` linear forms `ξ ↦ ∑ i, v i j * ξ i` have coefficients of total absolute value at
most `U`, and if `l ^ μ < (X + 1) ^ ν`, then some nonzero integer vector `ξ` with entries
bounded by `X` makes all the forms at most `U * X / l` in absolute value.

The proof is Dirichlet's box principle: the `(X + 1) ^ ν` vectors of the box `[0, X] ^ ν` are
sent to `l ^ μ` boxes, so two of them collide, and their difference is the required `ξ`. -/
theorem exists_int_vec_abs_le_of_pow_lt (v : Fin ν → Fin μ → ℝ) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ j, ∑ i, |v i j| ≤ U) {X l : ℕ} (hX : 0 < X) (hl : 0 < l)
    (hcard : (l : ℝ) ^ μ < ((X : ℝ) + 1) ^ ν) :
    ∃ ξ : Fin ν → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧
      ∀ j, |∑ i, v i j * (ξ i : ℝ)| ≤ U * X / l := by
  classical
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hν : 0 < ν := by
    rcases Nat.eq_zero_or_pos ν with h | h
    · subst h
      simp only [pow_zero] at hcard
      exact absurd (one_le_pow₀ hlR) (not_le.2 hcard)
    · exact h
  rcases hU0.eq_or_lt with hU00 | hUpos
  · -- Degenerate case: all coefficients vanish, so any nonzero vector in the box works.
    have hv0 : ∀ i j, v i j = 0 := by
      intro i j
      have hnn : ∀ k ∈ Finset.univ, (0 : ℝ) ≤ |v k j| := fun k _ => abs_nonneg _
      have h1 : ∑ k, |v k j| = 0 :=
        le_antisymm (by rw [hU00]; exact hU j) (Finset.sum_nonneg hnn)
      exact abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 i (Finset.mem_univ i))
    refine ⟨fun i => if i = ⟨0, hν⟩ then 1 else 0, fun h => ?_, fun i => ?_, fun j => ?_⟩
    · simpa using congrFun h ⟨0, hν⟩
    · have hX' : (1 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX
      by_cases h : i = ⟨0, hν⟩ <;> simp [h, hX']
    · simp [hv0, ← hU00]
  · -- The `l` boxes have length `c`.
    set c : ℝ := (X : ℝ) * U / l with hcdef
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hc : 0 < c := div_pos (mul_pos hXR hUpos) (by linarith)
    have hlc : (l : ℝ) * c = (X : ℝ) * U := by rw [hcdef]; field_simp
    set sh : Fin μ → ℝ := fun j => ∑ i, max 0 (-(v i j)) with hsh
    set a : (Fin ν → ℤ) → Fin μ → ℝ :=
      fun ξ j => (∑ i, v i j * (ξ i : ℝ)) + (X : ℝ) * sh j with ha
    have haeq : ∀ ξ j, a ξ j = ∑ i, (v i j * (ξ i : ℝ) + (X : ℝ) * max 0 (-(v i j))) := by
      intro ξ j
      simp only [ha, hsh, Finset.mul_sum, Finset.sum_add_distrib]
    set B : Finset (Fin ν → ℤ) := Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (X : ℤ) with hB
    have hBmem : ∀ ξ, ξ ∈ B ↔ ∀ i, 0 ≤ ξ i ∧ ξ i ≤ (X : ℤ) := by
      intro ξ; simp [hB, Fintype.mem_piFinset, Finset.mem_Icc]
    -- `a ξ j` lies in `[0, l * c]` for every `ξ` in the box.
    have ha0 : ∀ ξ ∈ B, ∀ j, 0 ≤ a ξ j := by
      intro ξ hξ j
      rw [haeq]
      refine Finset.sum_nonneg fun i _ => ?_
      obtain ⟨h1, h2⟩ := (hBmem ξ).1 hξ i
      have hx1 : (0 : ℝ) ≤ (ξ i : ℝ) := by exact_mod_cast h1
      have hx2 : ((ξ i : ℝ)) ≤ (X : ℝ) := by exact_mod_cast h2
      rcases le_or_gt 0 (v i j) with h | h
      · rw [max_eq_left (by linarith)]; nlinarith
      · rw [max_eq_right (by linarith)]; nlinarith
    have haU : ∀ ξ ∈ B, ∀ j, a ξ j ≤ (l : ℝ) * c := by
      intro ξ hξ j
      rw [hlc, haeq]
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin ν)),
          v i j * (ξ i : ℝ) + (X : ℝ) * max 0 (-(v i j)) ≤ (X : ℝ) * |v i j| := by
        intro i _
        obtain ⟨h1, h2⟩ := (hBmem ξ).1 hξ i
        have hx1 : (0 : ℝ) ≤ (ξ i : ℝ) := by exact_mod_cast h1
        have hx2 : ((ξ i : ℝ)) ≤ (X : ℝ) := by exact_mod_cast h2
        rcases le_or_gt 0 (v i j) with h | h
        · rw [max_eq_left (by linarith), abs_of_nonneg h]; nlinarith
        · rw [max_eq_right (by linarith), abs_of_neg h]; nlinarith
      calc ∑ i, (v i j * (ξ i : ℝ) + (X : ℝ) * max 0 (-(v i j)))
          ≤ ∑ i, (X : ℝ) * |v i j| := Finset.sum_le_sum hterm
        _ = (X : ℝ) * ∑ i, |v i j| := by rw [Finset.mul_sum]
        _ ≤ (X : ℝ) * U := mul_le_mul_of_nonneg_left (hU j) hXR.le
    -- Dirichlet's box principle.
    set box : (Fin ν → ℤ) → Fin μ → Fin l :=
      fun ξ j => ⟨min (l - 1) ⌊a ξ j / c⌋.toNat, by omega⟩ with hbox
    have hlt : (Finset.univ : Finset (Fin μ → Fin l)).card < B.card := by
      have h1 : (Finset.univ : Finset (Fin μ → Fin l)).card = l ^ μ := by simp
      have h2 : B.card = (X + 1) ^ ν := by simp [hB, Fintype.card_piFinset, Int.card_Icc]
      rw [h1, h2]
      have : ((l ^ μ : ℕ) : ℝ) < (((X + 1) ^ ν : ℕ) : ℝ) := by push_cast; exact hcard
      exact_mod_cast this
    obtain ⟨ξ', hξ'B, ξ'', hξ''B, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun ξ _ => Finset.mem_univ (box ξ))
    refine ⟨ξ' - ξ'', sub_ne_zero.2 hne, fun i => ?_, fun j => ?_⟩
    · obtain ⟨h1, h2⟩ := (hBmem ξ').1 hξ'B i
      obtain ⟨h3, h4⟩ := (hBmem ξ'').1 hξ''B i
      simp only [Pi.sub_apply, abs_le]
      omega
    · have hcol : min (l - 1) ⌊a ξ' j / c⌋.toNat = min (l - 1) ⌊a ξ'' j / c⌋.toNat := by
        simpa [hbox, Fin.ext_iff] using congrFun heq j
      obtain ⟨p1, p2⟩ := mem_box hc hl (ha0 ξ' hξ'B j) (haU ξ' hξ'B j)
      obtain ⟨q1, q2⟩ := mem_box hc hl (ha0 ξ'' hξ''B j) (haU ξ'' hξ''B j)
      rw [hcol] at p1 p2
      have hsub : ∑ i, v i j * (((ξ' - ξ'') i : ℤ) : ℝ) = a ξ' j - a ξ'' j := by
        simp only [ha, Pi.sub_apply, Int.cast_sub, mul_sub]
        rw [Finset.sum_sub_distrib]
        ring
      have hcU : c = U * X / l := by rw [hcdef]; ring_nf
      rw [hsub, abs_le, ← hcU]
      constructor <;> linarith

end ThueSiegel
