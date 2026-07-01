/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# `ℝ` is a real closed field

The Artin development (`ArtinTransfer`, `ArtinBridge`, `Artin`) is now machine-checked with **no
`sorry`**, modulo a single explicit hypothesis: quantifier elimination for the first-order theory of
real closed fields, `Artin.ModelTheory.Theory.RCF.HasQuantifierElimination`. That hypothesis is the
Tarski–Seidenberg core, provable via **Sturm's theorem** (sign changes determine root counts).

This file supplies the concrete ingredient the transfer needs on the base field: **`ℝ` is real
closed** (`Real.instIsRealClosed`), so that `modelRCF` makes `ℝ ⊨ Theory.RCF` and
`ArtinTransfer.realize_transfer_of_qe` applies with the elementary embedding `ℝ ↪ C`.

* `Real.isSquare_of_nonneg` — every nonnegative real is a square (via `Real.sqrt`);
* `Real.exists_isRoot_of_odd_natDegree` — odd-degree real polynomials have a root (opposite signs at
  `±∞` via the polynomial tendsto lemmas + the intermediate value theorem);
* `Real.instIsRealClosed` — assembled from the two via `IsRealClosed.of_linearOrderedField`.
-/

open Polynomial Filter Topology

namespace Artin

/-- Every nonnegative real is a square. -/
theorem Real.isSquare_of_nonneg {x : ℝ} (hx : 0 ≤ x) : IsSquare x :=
  ⟨Real.sqrt x, (Real.mul_self_sqrt hx).symm⟩

/-- An odd-degree real polynomial has a root. Elementary: the polynomial is unbounded of opposite
signs at `±∞`, so by the intermediate value theorem it vanishes somewhere. (Standard IVT argument;
isolated here.) -/
theorem Real.exists_isRoot_of_odd_natDegree {f : ℝ[X]} (hf : Odd f.natDegree) :
    ∃ x, f.IsRoot x := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.1 hf.pos
  have hcnd : (f.comp (-X)).natDegree = f.natDegree := by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  have hcdeg : 0 < (f.comp (-X)).degree :=
    natDegree_pos_iff_degree_pos.1 (by rw [hcnd]; exact hf.pos)
  have hclc : (f.comp (-X)).leadingCoeff = -f.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_neg, natDegree_X]; norm_num), leadingCoeff_neg,
      leadingCoeff_X, hf.neg_one_pow, mul_neg_one]
  obtain ⟨a, b, ha, hb⟩ : ∃ a b : ℝ, f.eval a ≤ 0 ∧ 0 ≤ f.eval b := by
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.2 hf0) with hlc | hlc
    · obtain ⟨a, ha⟩ := ((f.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc.le).eventually
        (eventually_le_atBot 0)).exists
      obtain ⟨b, hb⟩ := (((f.comp (-X)).tendsto_atTop_of_leadingCoeff_nonneg hcdeg
        (by rw [hclc]; linarith)).eventually (eventually_ge_atTop 0)).exists
      exact ⟨a, -b, ha, by simpa [eval_comp] using hb⟩
    · obtain ⟨b, hb⟩ := ((f.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le).eventually
        (eventually_ge_atTop 0)).exists
      obtain ⟨a, ha⟩ := (((f.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hcdeg
        (by rw [hclc]; linarith)).eventually (eventually_le_atBot 0)).exists
      exact ⟨-a, b, by simpa [eval_comp] using ha, hb⟩
  obtain ⟨c, hc⟩ := intermediate_value_univ₂ f.continuous continuous_const ha hb
  exact ⟨c, hc⟩

/-- `ℝ` is a real closed field. -/
instance Real.instIsRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField (fun {_} => Real.isSquare_of_nonneg)
    (fun {_} => Real.exists_isRoot_of_odd_natDegree)

end Artin
