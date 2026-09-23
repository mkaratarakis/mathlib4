/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.SiegelsLemma

/-!
# Thue–Siegel's lemma, inequality form

`Mathlib/NumberTheory/SiegelsLemma.lean` provides the *equation* form of Thue–Siegel's lemma:
an underdetermined integral linear system has a small nonzero integral solution.  This file
provides the *inequality* form, in which the linear forms are real (not necessarily integral)
and one only asks that they take small values.  It is Lemma 4.11 of [waldschmidt2000] and is
the form used to construct auxiliary functions.

Both are instances of Dirichlet's box principle; neither implies the other, since here the
coefficients are arbitrary reals.

This file belongs in `Mathlib/NumberTheory/SiegelsLemma.lean`.

## Main statements

* `exists_int_vec_abs_le_of_pow_lt`: given real numbers `v i j` whose columns have
  `ℓ¹`-norm at most `U`, and positive integers `X`, `l` with `l ^ μ < (X + 1) ^ ν`, there is a
  nonzero integer vector `ξ` with `|ξ i| ≤ X` and `|∑ i, v i j * ξ i| ≤ U * X / l` for every `j`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic
  Groups*][waldschmidt2000], Lemma 4.11
-/

@[expose] public section

open Finset

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
    · by_cases h : i = ⟨0, hν⟩ <;> simp [h] <;> omega
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
