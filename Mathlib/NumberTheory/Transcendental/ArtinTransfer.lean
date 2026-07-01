/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

/-!
# The Tarski transfer for Artin's theorem, framed in first-order model theory

`Artin.exists_neg_eval_of_real_closed` — the one deep `sorry` behind `Artin.artin` — says a
polynomial inequality solvable in a real closed field `C ⊇ ℝ` is already solvable in `ℝ`. This file
**reframes** that transfer inside Mathlib's first-order model theory and reduces it to two explicit,
separable obligations, isolating the genuinely deep part:

1. `Artin.ModelTheory.realClosed_elementaryEmbedding` — **model completeness of real closed
   fields**: `ℝ` embeds *elementarily* into any real closed field extending it (language of ordered
   rings). This is the Tarski–Seidenberg content; it is where a proof that the theory of real closed
   fields has quantifier elimination plugs in (e.g. the `model-theory/quantifier-elimination`
   criteria applied to a theory `Theory.RCF`).

2. `Artin.ModelTheory.elementaryEmbedding_reflect_exists_neg` — the **algebra ↔ logic dictionary**:
   an elementary embedding reflects the existential inequality `∃ x, f(x) < 0`. To be built from
   `FirstOrder.Ring`'s polynomial↔term bridge (`termOfFreeCommRing`) plus the order relation, by
   encoding `∃ x, f(x) < 0` as a first-order formula with the coefficients of `f` as parameters.

`exists_neg_eval_of_real_closed` is then **proved** from these two (see the theorem at the end), so
the remaining work is exactly (1) and (2). Both are currently `sorry`.
-/

open FirstOrder Language MvPolynomial

namespace Artin.ModelTheory

/-- The first-order language of ordered rings: the ring operations together with `≤`. -/
abbrev orderedRing : Language := Language.ring.sum Language.order

variable {σ : Type*}

/-- The ring first-order structure on an ordered field, compatible with its ring operations.
Presented as the two component structures (rather than a packaged sum structure) so that the sum
structure `orderedRing.Structure` and `LHom.sumInl.IsExpansionOn` resolve automatically. -/
noncomputable instance compatibleRingOfOrderedField (M : Type*) [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] : Ring.CompatibleRing M :=
  Ring.compatibleRingOfRing M

/-- The order first-order structure on an ordered field. -/
instance orderStructureOfOrderedField (M : Type*) [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] : Language.order.Structure M :=
  Language.orderStructure M

/-- The order structure interprets `≤` as the field's order (so linear-order axioms hold). -/
instance orderedStructureOfOrderedField (M : Type*) [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] : orderedRing.OrderedStructure M :=
  ⟨fun _ => Iff.rfl⟩

/-- **Model completeness of real closed fields (the isolated deep obligation).** Every real closed
field `C` with a ring embedding of `ℝ` receives `ℝ` as an *elementary* substructure in the language
of ordered rings. Equivalent to quantifier elimination for the theory of real closed fields, and the
single genuinely deep ingredient (the place to apply the `model-theory/quantifier-elimination`
criteria to a theory `Theory.RCF`). -/
theorem realClosed_elementaryEmbedding
    (C : Type*) [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]
    (ψ : ℝ →+* C) :
    ∃ g : ℝ ↪ₑ[orderedRing] C, ∀ r, g r = ψ r :=
  sorry

/-! The eval↔formula bridge and the assembled transfer `exists_neg_eval_of_real_closed` are proved
in `Mathlib.NumberTheory.Transcendental.ArtinBridge`, which has the free-commutative-ring encoding
machinery. Only `realClosed_elementaryEmbedding` (RCF model completeness) remains a `sorry`. -/

end Artin.ModelTheory
