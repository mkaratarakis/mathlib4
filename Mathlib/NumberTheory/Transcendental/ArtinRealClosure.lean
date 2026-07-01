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
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Toward finishing RCF model completeness: real closure and its uniqueness

The lone remaining `sorry` of the Artin development is the **RCF back-and-forth** (the Tarski–Vaught
test in `ArtinTransfer.realClosed_elementaryEmbedding`): an existential formula realized in a real
closed `C ⊇ ℝ` over `ℝ`-parameters is realized in `ℝ`. This file scaffolds the path to it.

## Decomposition (blueprint)

1. **`Real.instIsRealClosed`** — `ℝ` is real closed (nonnegatives are squares via `Real.sqrt`;
   odd-degree polynomials have roots via the intermediate value theorem). This makes `ℝ ⊨
   Theory.RCF`
   and pins down the base of the back-and-forth.

2. **Real closure uniqueness** (`realClosure_unique`, the deep obligation): two real closed fields
   algebraic over an ordered field `F`, both extending `F` order-preservingly, are `F`-order-
   isomorphic. This is the Tarski–Seidenberg core, provable via **Sturm's theorem** (sign changes
   determine root counts), which is not yet in Mathlib.

3. **The reduction** back-and-forth ⟸ uniqueness (model theory): given `a ∈ C`, the real closure of
   `ℝ(a)` embeds into both `ℝ` and `C` over `ℝ`; uniqueness matches a real witness `b` to `a`,
   transferring realization of the quantifier-free part. Reusable pieces:
   `Hilbert17Blueprint.exists_realClosure`, `IsRealClosed.nonneg_iff_isSquare`,
   `IsRealClosed.exists_isRoot_of_odd_natDegree`, and the term/formula machinery in `ArtinBridge`.

Step 1 is provided here (`ℝ` real closed); step 2 is stated precisely; step 3 (and the Sturm engine
for step 2) is the remaining frontier.
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

/-- **Uniqueness of the real closure (the deep obligation).** Two real closed fields, each algebraic
over an ordered field `F` and extending its order (via order-preserving algebra maps), are
isomorphic
over `F` as ordered fields. This is the Tarski–Seidenberg core; to be proved via Sturm's theorem
(sign changes determine root counts). -/
theorem realClosure_unique {F R₁ R₂ : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R₁] [LinearOrder R₁] [IsStrictOrderedRing R₁] [IsRealClosed R₁] [Algebra F R₁]
    [Algebra.IsAlgebraic F R₁]
    [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂] [IsRealClosed R₂] [Algebra F R₂]
    [Algebra.IsAlgebraic F R₂]
    (hmono₁ : Monotone (algebraMap F R₁)) (hmono₂ : Monotone (algebraMap F R₂)) :
    ∃ φ : R₁ ≃+* R₂, Monotone φ ∧ ∀ x : F, φ (algebraMap F R₁ x) = algebraMap F R₂ x :=
  sorry

end Artin
