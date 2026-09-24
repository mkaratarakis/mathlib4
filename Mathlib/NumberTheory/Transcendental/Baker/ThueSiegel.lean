/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.SiegelsLemma

/-!
# Thue-Siegel's lemma, inequality form

`Mathlib/NumberTheory/SiegelsLemma.lean` gives the *equation* form of Thue-Siegel's lemma: an
underdetermined integral linear system has a small nonzero integral solution.  This file gives
the *inequality* form, in which the linear forms have arbitrary real coefficients and one only
asks that they take small values.  It is Lemma 4.11 of [waldschmidt2000] and is the form used
to construct auxiliary functions.

Both are instances of Dirichlet's box principle; neither implies the other, since here the
coefficients need not be integral.

## Main statements

* `ThueSiegel.exists_int_vec_abs_le_of_pow_lt`: given real numbers `v i j` whose columns have
  `ℓ¹`-norm at most `U`, and positive integers `X`, `l` with
  `l ^ card κ < (X + 1) ^ card ι`, there is a nonzero integer vector `ξ` with `|ξ i| ≤ X` and
  `|∑ i, v i j * ξ i| ≤ U * X / l` for every `j`.

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
theorem exists_int_vec_abs_le_of_pow_lt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → κ → ℝ) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ j, ∑ i, |v i j| ≤ U) {X l : ℕ} (hX : 0 < X) (hl : 0 < l)
    (hcard : (l : ℝ) ^ Fintype.card κ < ((X : ℝ) + 1) ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧
      ∀ j, |∑ i, v i j * (ξ i : ℝ)| ≤ U * X / l := by
  classical
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hν : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · exfalso
      rw [Fintype.card_eq_zero (α := ι), pow_zero] at hcard
      exact absurd (one_le_pow₀ hlR) (not_le.2 hcard)
    · exact h
  have := hν
  set i₀ : ι := Classical.arbitrary ι with hi₀
  rcases hU0.eq_or_lt with hU00 | hUpos
  · -- Degenerate case: all coefficients vanish, so any nonzero vector in the box works.
    have hv0 : ∀ i j, v i j = 0 := by
      intro i j
      have hnn : ∀ k ∈ Finset.univ, (0 : ℝ) ≤ |v k j| := fun k _ => abs_nonneg _
      have h1 : ∑ k, |v k j| = 0 :=
        le_antisymm (by rw [hU00]; exact hU j) (Finset.sum_nonneg hnn)
      exact abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 i (Finset.mem_univ i))
    refine ⟨fun i => if i = i₀ then 1 else 0, fun h => ?_, fun i => ?_, fun j => ?_⟩
    · simpa using congrFun h i₀
    · have hX' : (1 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX
      by_cases h : i = i₀ <;> simp [h, hX']
    · simp [hv0, ← hU00]
  · -- The `l` boxes have length `c`.
    set c : ℝ := (X : ℝ) * U / l with hcdef
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hc : 0 < c := div_pos (mul_pos hXR hUpos) (by linarith)
    have hlc : (l : ℝ) * c = (X : ℝ) * U := by rw [hcdef]; field_simp
    set sh : κ → ℝ := fun j => ∑ i, max 0 (-(v i j)) with hsh
    set a : (ι → ℤ) → κ → ℝ :=
      fun ξ j => (∑ i, v i j * (ξ i : ℝ)) + (X : ℝ) * sh j with ha
    have haeq : ∀ ξ j, a ξ j = ∑ i, (v i j * (ξ i : ℝ) + (X : ℝ) * max 0 (-(v i j))) := by
      intro ξ j
      simp only [ha, hsh, Finset.mul_sum, Finset.sum_add_distrib]
    set B : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (X : ℤ) with hB
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
      have hterm : ∀ i ∈ (Finset.univ : Finset (ι)),
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
    set box : (ι → ℤ) → κ → Fin l :=
      fun ξ j => ⟨min (l - 1) ⌊a ξ j / c⌋.toNat, by omega⟩ with hbox
    have hlt : (Finset.univ : Finset (κ → Fin l)).card < B.card := by
      have h1 : (Finset.univ : Finset (κ → Fin l)).card = l ^ Fintype.card κ := by simp
      have h2 : B.card = (X + 1) ^ Fintype.card ι := by
        simp [hB, Fintype.card_piFinset, Int.card_Icc]
      rw [h1, h2]
      have : ((l ^ Fintype.card κ : ℕ) : ℝ) < (((X + 1) ^ Fintype.card ι : ℕ) : ℝ) := by
        push_cast; exact hcard
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

/-- **Thue-Siegel's lemma for complex forms** (Lemma 4.12 of [waldschmidt2000]).

The same box principle applied to the real and imaginary parts separately: `2 * card κ` real
forms in place of `card κ` complex ones.  The factor `√2` is the cost of recombining a complex
number from bounds on its real and imaginary parts. -/
theorem exists_int_vec_norm_le_of_pow_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℂ) {U V : ℝ} (hU : ∀ j, ∑ i, ‖u i j‖ ≤ Real.exp U)
    {X : ℕ} (hX : 0 < X) (hι : 0 < Fintype.card ι)
    (hcard : (Real.sqrt 2 * X * Real.exp (U + V) + 1) ^ (2 * Fintype.card κ)
      ≤ ((X : ℝ) + 1) ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧
      ∀ j, ‖∑ i, u i j * (ξ i : ℂ)‖ ≤ Real.exp (-V) := by
  classical
  set t : ℝ := Real.sqrt 2 * X * Real.exp (U + V) with ht
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have ht0 : 0 < t := by
    rw [ht]; positivity
  set l : ℕ := ⌈t⌉₊ with hl
  have hlt : t ≤ (l : ℝ) := Nat.le_ceil t
  have hlt1 : (l : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0.le
  have hl0 : 0 < l := Nat.ceil_pos.2 ht0
  -- the `2 * card κ` real forms
  set v : ι → κ × Bool → ℝ := fun i p => if p.2 then (u i p.1).im else (u i p.1).re with hv
  have hUv : ∀ p : κ × Bool, ∑ i, |v i p| ≤ Real.exp U := by
    rintro ⟨j, b⟩
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hU j)
    cases b
    · simpa [hv] using Complex.abs_re_le_norm (u i j)
    · simpa [hv] using Complex.abs_im_le_norm (u i j)
  have hcard' : (l : ℝ) ^ Fintype.card (κ × Bool) < ((X : ℝ) + 1) ^ Fintype.card ι := by
    rw [Fintype.card_prod, Fintype.card_bool]
    rcases Nat.eq_zero_or_pos (Fintype.card κ) with h0 | hpos
    · rw [h0, Nat.zero_mul, pow_zero]
      calc (1 : ℝ) < (X : ℝ) + 1 := by linarith
        _ = ((X : ℝ) + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((X : ℝ) + 1) ^ Fintype.card ι := by
            refine pow_le_pow_right₀ (by linarith) hι
    · refine lt_of_lt_of_le ?_ hcard
      have h2 : 0 < Fintype.card κ * 2 := by positivity
      exact pow_lt_pow_left₀ hlt1 (by positivity) (by omega) |>.trans_eq
        (by rw [mul_comm])
  obtain ⟨ξ, hξ0, hξX, hξv⟩ :=
    ThueSiegel.exists_int_vec_abs_le_of_pow_lt v (Real.exp_pos U).le hUv hX hl0 hcard'
  refine ⟨ξ, hξ0, hξX, fun j => ?_⟩
  have hre : (∑ i, u i j * (ξ i : ℂ)).re = ∑ i, v i (j, false) * (ξ i : ℝ) := by
    simp [hv, Complex.re_sum, Complex.mul_re]
  have him : (∑ i, u i j * (ξ i : ℂ)).im = ∑ i, v i (j, true) * (ξ i : ℝ) := by
    simp [hv, Complex.im_sum, Complex.mul_im]
  have hmax : max |(∑ i, u i j * (ξ i : ℂ)).re| |(∑ i, u i j * (ξ i : ℂ)).im|
      ≤ Real.exp U * X / l := by
    rw [hre, him]
    exact max_le (hξv (j, false)) (hξv (j, true))
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have key : Real.exp (-V) * t = Real.sqrt 2 * (Real.exp U * (X : ℝ)) := by
    rw [ht, Real.exp_add, Real.exp_neg]
    have : Real.exp V ≠ 0 := (Real.exp_pos V).ne'
    field_simp
  have hfin : Real.sqrt 2 * (Real.exp U * X / l) ≤ Real.exp (-V) := by
    rw [mul_div_assoc', div_le_iff₀ hlR, ← key]
    exact mul_le_mul_of_nonneg_left hlt (Real.exp_pos _).le
  calc ‖∑ i, u i j * (ξ i : ℂ)‖ ≤ Real.sqrt 2 * max _ _ :=
        Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (Real.exp U * X / l) := by gcongr
    _ ≤ Real.exp (-V) := hfin
