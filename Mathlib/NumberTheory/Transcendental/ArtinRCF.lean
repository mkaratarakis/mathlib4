/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.ModelTheory.Order
import Mathlib.NumberTheory.Transcendental.ArtinTransfer

/-!
# The first-order theory of ordered fields (towards `Theory.RCF`)

Part A of `ArtinBlueprint`: building the theory of real closed fields in the language of ordered
rings `Artin.ModelTheory.orderedRing = Language.ring.sum Language.order`, mirroring
`FirstOrder.Language.Theory.field`.

This file provides `Artin.ModelTheory.Theory.orderedField` — field axioms + linear-order axioms +
the two order-compatibility axioms (`0 ≤ a → 0 ≤ b → 0 ≤ a·b` and `a ≤ b → a + c ≤ b + c`). The real
closed axioms (`x` or `-x` is a square; odd-degree monic polynomials have roots) are added on top to
form `Theory.RCF` in a follow-up.
-/

open FirstOrder Language

namespace Artin.ModelTheory

/-- The atomic formula `t₁ ≤ t₂` between two ring terms, in the ordered-ring language. -/
def rle {n : ℕ} (t₁ t₂ : Language.ring.Term (Empty ⊕ Fin n)) :
    orderedRing.BoundedFormula Empty n :=
  (LHom.sumInl.onTerm t₁).le (LHom.sumInl.onTerm t₂)

/-- The theory of ordered fields, over the language of ordered rings. -/
def Theory.orderedField : orderedRing.Theory :=
  LHom.sumInl.onTheory Language.Theory.field ∪
  orderedRing.linearOrderTheory ∪
  { -- `0 ≤ a → 0 ≤ b → 0 ≤ a * b`
    ∀' ∀' (rle 0 (&0) ⟹ rle 0 (&1) ⟹ rle 0 (&0 * &1)),
    -- `a ≤ b → a + c ≤ b + c`
    ∀' ∀' ∀' (rle (&0) (&1) ⟹ rle (&0 + &2) (&1 + &2)) }

/-- The atomic formula `t₁ = t₂` between two ring terms, in the ordered-ring language. -/
def req {n : ℕ} (t₁ t₂ : Language.ring.Term (Empty ⊕ Fin n)) :
    orderedRing.BoundedFormula Empty n :=
  (LHom.sumInl.onTerm t₁).bdEqual (LHom.sumInl.onTerm t₂)

/-- The real closed axioms over the language of ordered rings: every element or its negation is a
square, and every odd-degree monic polynomial has a root (the latter reusing the algebraic
`FirstOrder.Field.genericMonicPolyHasRoot` sentences, restricted to odd degrees). -/
def Theory.realClosedAxioms : orderedRing.Theory :=
  {∀' ∃' (req (&0) (&1 * &1) ⊔ req (-&0) (&1 * &1))} ∪
    LHom.sumInl.onSentence '' (FirstOrder.Field.genericMonicPolyHasRoot '' {n | Odd n})

/-- The theory of real closed fields, in the language of ordered rings. -/
def Theory.RCF : orderedRing.Theory := Theory.orderedField ∪ Theory.realClosedAxioms

/-! ## Models: `ℝ` and every real closed field satisfy `Theory.RCF` -/

section Models

variable (M : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [IsRealClosed M]

/-- Every real closed field is a model of `Theory.RCF`. The field and linear-order parts resolve by
instance; the two order-compatibility sentences and the real-closed axioms are realized directly. -/
instance modelRCF : (Theory.RCF).Model M := by
  have hfield : ((LHom.sumInl : Language.ring →ᴸ orderedRing).onTheory
      Language.Theory.field).Model M :=
    (LHom.onTheory_model (LHom.sumInl : Language.ring →ᴸ orderedRing) Language.Theory.field).2
      inferInstance
  rw [Theory.RCF, Theory.orderedField]
  refine Theory.model_union_iff.mpr ⟨Theory.model_union_iff.mpr
    ⟨Theory.model_union_iff.mpr ⟨hfield, inferInstance⟩, ?_⟩, ?_⟩
  · -- order-compatibility axioms
    rw [Theory.model_iff]
    intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl
    · -- `0 ≤ a → 0 ≤ b → 0 ≤ a * b`
      simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
        BoundedFormula.realize_imp, rle, Term.realize_le, LHom.realize_onTerm,
        Ring.realize_mul, Ring.realize_zero]
      intro a b
      exact mul_nonneg
    · -- `a ≤ b → a + c ≤ b + c`
      simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
        BoundedFormula.realize_imp, rle, Term.realize_le, LHom.realize_onTerm,
        Ring.realize_add, Term.realize_var, Sum.elim_inr]
      intro a b c h
      linarith
  · -- real-closed axioms
    rw [Theory.realClosedAxioms, Theory.model_union_iff]
    refine ⟨?_, ?_⟩
    · -- `∀ x, ∃ y, x = y*y ∨ -x = y*y`
      rw [Theory.model_iff]
      intro φ hφ
      simp only [Set.mem_singleton_iff] at hφ
      subst hφ
      simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
        BoundedFormula.realize_ex, BoundedFormula.realize_sup, req, BoundedFormula.realize_bdEqual,
        LHom.realize_onTerm, Ring.realize_mul, Ring.realize_neg, Term.realize_var]
      intro x
      rcases IsRealClosed.isSquare_or_isSquare_neg x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨y, Or.inl hy⟩
      · exact ⟨y, Or.inr hy⟩
    · -- every odd-degree monic polynomial has a root
      rw [Theory.model_iff]
      intro φ hφ
      simp only [Set.mem_image, Set.mem_setOf_eq] at hφ
      obtain ⟨_, ⟨n, hn, rfl⟩, rfl⟩ := hφ
      rw [LHom.realize_onSentence, Field.realize_genericMonicPolyHasRoot]
      intro p
      obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := p.1)
        (by rw [p.2.2]; exact hn)
      exact ⟨x, hx⟩

end Models

end Artin.ModelTheory
