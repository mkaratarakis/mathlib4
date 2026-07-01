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
  {∀' ∃' (req (&1) (&0 * &0) ⊔ req (-&1) (&0 * &0))} ∪
    LHom.sumInl.onSentence '' (FirstOrder.Field.genericMonicPolyHasRoot '' {n | Odd n})

/-- The theory of real closed fields, in the language of ordered rings. -/
def Theory.RCF : orderedRing.Theory := Theory.orderedField ∪ Theory.realClosedAxioms

end Artin.ModelTheory
