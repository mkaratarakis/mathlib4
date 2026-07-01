/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.ArtinTransfer
import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
import Mathlib.ModelTheory.Satisfiability

/-!
# Blueprint: finishing Artin's theorem — RCF model completeness and the eval↔formula bridge

`Artin.artin` (scalar Hilbert 17) and its `Artin.exists_neg_eval_of_real_closed` are complete modulo
the two model-theoretic obligations in `ArtinTransfer.lean`:

* `Artin.ModelTheory.realClosed_elementaryEmbedding` — **RCF model completeness** (`ℝ ↪ₑ` any real
  closed extension), and
* `Artin.ModelTheory.elementaryEmbedding_reflect_exists_neg` — the **eval↔formula bridge**.

This file is the *blueprint* for discharging both: a decomposition into individually-attackable
sub-lemmas, each annotated with the exact reusable Mathlib declarations found by an extensive survey
of `Mathlib/ModelTheory/*`, `Mathlib/FieldTheory/IsRealClosed`, and this branch's own real-closure
development (`Hilbert17*`). It also flags the two genuine gaps (real-closure uniqueness; the general
polynomial→formula encoding).

## Part A — RCF model completeness (`realClosed_elementaryEmbedding`)

Mirror the algebraically-closed-fields development in
`Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean`.

**A1. The theory `Theory.RCF : Language.orderedRing.Theory`.** Field axioms + linear-order axioms +
two schemes: "`x` or `-x` is a square" and, for each odd `n`, "every monic degree-`n` polynomial has
a root". Reuse: `Theory.ACF`, `Theory.field`, `Language.order.linearOrderTheory`,
`FirstOrder.Field.genericMonicPoly`/`genericMonicPolyHasRoot` (the coefficients-as-variables
pattern),
`FirstOrder.Ring.termOfFreeCommRing`.

**A2. `ℝ` and a real closed `C` are models of `Theory.RCF`.** Reuse: `IsRealClosed`,
`IsRealClosed.nonneg_iff_isSquare`, `IsRealClosed.isSquare_or_isSquare_neg`,
`IsRealClosed.exists_isRoot_of_odd_natDegree`, and the `realize_genericMonicPolyHasRoot` proof
pattern (term ↔ evaluation).

**A3. `Theory.RCF` is model complete** — i.e. every embedding between its models is elementary.
This is the deep Tarski–Seidenberg core. Route: the Tarski–Vaught test
`FirstOrder.Language.Embedding.isElementary_of_exists` (`ModelTheory/ElementaryMaps.lean:245`)
reduces it to: for RCF models `M ↪ N` sharing a substructure, an existential formula realized in `N`
is realized in `M`. Discharging *that* is the **RCF back-and-forth**, resting on:
  * uniqueness of the real closure of an ordered field, up to unique order-isomorphism — **GAP**:
    Mathlib/this branch only have *existence* (`Hilbert17Blueprint.exists_realClosure`,
    `exists_isRealClosed_extension`); the uniqueness/`ElementaryEquivalence` is not formalized;
  * sign conditions / the intermediate value property, via
  `IsRealClosed.exists_isRoot_of_odd_natDegree`
    and `IsRealClosed.nonneg_iff_isSquare`;
  * simple ordered extensions and order-extension of preorderings (`RingPreordering.toLinearOrder`,
    `RingPreordering.isSumSq_of_forall_mem`, `Hilbert17Blueprint.good_adjoinRoot_sqrt`).

  *Note on the ACF analogy.* ACF proves **completeness** via categoricity + Łoś–Vaught
  (`Cardinal.Categorical.isComplete`, `ACF_categorical`, `ACF_isComplete`). That gives elementary
  *equivalence* of all models, which is **weaker** than the elementary *embedding* we need. Model
  completeness must come from quantifier elimination / the back-and-forth, not categoricity alone.
  Quantifier elimination for RCF (`BOUN-MATH490/mathlib4#3`,
  `ModelTheory/QuantifierElimination.lean`) is the intended engine: `HasQuantifierElimination` + a
  common submodel ⟹ model complete; its criteria
  (`hasQuantifierElimination_of_isElementaryExtensionPair`,
  `hasQuantifierElimination_of_exists_realize_of_embeddings`) consume exactly the back-and-forth
  above.

**A4. `realClosed_elementaryEmbedding`.** Instantiate model completeness at `ℝ ↪ C`, where the
underlying map is the given `ψ : ℝ →+* C` (order-preserving as a ring hom out of `ℝ`). Requires the
coherence `⇑g = ψ`.

## Part B — the eval↔formula bridge (`elementaryEmbedding_reflect_exists_neg`)

This is self-contained and mechanical given Mathlib's model-theory API; no new mathematics.

**B1. Encode `∃ x, f(x) < 0` as a first-order formula** over `Language.orderedRing`, with the
coefficients of `f` as parameters (a `Formula` over the coefficient-index type, or via
`Language.withConstants`). Reuse: `FirstOrder.Ring.termOfFreeCommRing` (polynomial→term),
`FirstOrder.Language.Term.lt` (`t₁ < t₂` as a `BoundedFormula`, via `Language.order`),
`FirstOrder.Language.BoundedFormula.ex` (existential), `Language.ring.sum Language.order` +
`LHom.sumInl/sumInr`/`LHom.onTerm` to place ring terms and the order relation in the joint language.
Model the construction on `FirstOrder.Field.genericMonicPolyHasRoot`.

**B2. Realization equals evaluation.** Reuse: `FirstOrder.Ring.realize_termOfFreeCommRing`
(`term.realize v = FreeCommRing.lift v`), `FirstOrder.Language.Term.realize_lt`
(`(t₁.lt t₂).Realize ↔ realize t₁ < realize t₂`), `FirstOrder.Language.BoundedFormula.realize_ex`.
Net: the formula realizes in an ordered field `M` (at coefficient assignment `c`) iff
`∃ x : σ → M, eval₂ c-as-hom x f < 0`.

**B3. Reflect along the elementary embedding.** Reuse:
`FirstOrder.Language.ElementaryEmbedding.map_formula` (or `map_boundedFormula`):
`φ.Realize (g ∘ v) ↔ φ.Realize v`. With `v` the real coefficients and `g = ψ`, "negative somewhere
in `C`" transfers to "negative somewhere in `ℝ`".

**Coherence.** B needs `⇑g = ψ` (the elementary embedding's map is the ring hom used by `eval₂`),
and
the standard ordered-ring structure on `ℝ`, `C` (`Artin.ModelTheory.structureOfOrderedField`), so
that `ψ` is a `Language.orderedRing`-embedding and `eval₂ ψ = eval ∘ (map ψ)`.

## Gaps summary

1. **Real-closure uniqueness** (Part A3) — up to unique order-isomorphism; the one genuinely missing
   piece of mathematics, needed for the back-and-forth. Everything else in Part A is assembly of
   existing `IsRealClosed`/`Hilbert17Blueprint` facts through the QE criteria.
2. **General polynomial→formula encoding** (Part B1) — `genericMonicPoly` handles one monic
univariate
   family; a general `MvPolynomial σ ℝ` needs its support/coefficients threaded as parameters.
   Purely
   mechanical.

## Reusable-declaration index (verbatim names)

* Model theory core: `FirstOrder.Language.ElementaryEmbedding` (`↪ₑ[L]`), `.map_formula`,
  `.map_boundedFormula`, `.map_sentence`, `Embedding.isElementary_of_exists` (Tarski–Vaught),
  `Theory.IsComplete`, `Cardinal.Categorical.isComplete` (Łoś–Vaught), `Theory.IsSatisfiable`.
* ACF template: `Theory.ACF`, `genericMonicPoly`, `genericMonicPolyHasRoot`,
  `realize_genericMonicPolyHasRoot`, `ACF_isSatisfiable`, `ACF_categorical`, `ACF_isComplete`.
* Bridge: `Ring.termOfFreeCommRing`, `Ring.realize_termOfFreeCommRing`, `Ring.compatibleRingOfRing`,
  `Language.order`, `IsOrdered.leSymb`, `Term.le`, `Term.lt`, `Term.realize_le`, `Term.realize_lt`,
  `BoundedFormula.ex`, `realize_ex`, `Formula.Realize`, `Language.sum`, `sumStructure`,
  `LHom.sumInl`, `LHom.sumInr`, `LHom.onTerm`, `Language.withConstants` (`L[[α]]`), `Language.con`.
* Real closed fields: `IsRealClosed`, `IsRealClosed.nonneg_iff_isSquare`,
  `IsRealClosed.isSquare_or_isSquare_neg`, `IsRealClosed.exists_isRoot_of_odd_natDegree`.
* This branch's real closure: `Hilbert17Blueprint.exists_realClosure`, `.RealClosure`,
  `.exists_isRealClosed_extension`, `.isRealClosed_of_maximal`, `.good_adjoinRoot_sqrt`,
  `RingPreordering.isSumSq_of_forall_mem`, `RingPreordering.toLinearOrder`.
-/
