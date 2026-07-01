/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.QuantifierElimination
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Tarski transfer for Artin's theorem, framed in first-order model theory

`Artin.exists_neg_eval_of_real_closed` — the deep ingredient behind `Artin.artin` — says a
polynomial inequality solvable in a real closed field `C ⊇ ℝ` is already solvable in `ℝ`. This file
**reframes** that transfer inside Mathlib's first-order model theory and discharges it, `sorry`-free,
down to a *single named hypothesis*: quantifier elimination for the theory of real closed fields.

The two ingredients:

1. `Artin.ModelTheory.realClosed_elementaryEmbedding` — **model completeness of real closed
   fields**: `ℝ` embeds *elementarily* into any real closed field extending it (language of ordered
   rings). This is **proved** here from `realize_transfer_of_qe`: given a theory `T` modelled by both
   `ℝ` and `C` with quantifier elimination (`T.HasQuantifierElimination`, e.g. `T = Theory.RCF`), an
   ordered-ring embedding of models is elementary. The Tarski–Vaught back-and-forth reduces to QE
   plus absoluteness of quantifier-free formulas along embeddings (`IsQF.realize_embedding`).

2. The **algebra ↔ logic dictionary** (in `ArtinBridge`): an elementary embedding reflects the
   existential inequality `∃ x, f(x) < 0`, built from `FirstOrder.Ring`'s polynomial↔term bridge
   (`termOfFreeCommRing`) plus the order relation.

`exists_neg_eval_of_real_closed` is then **proved** (in `ArtinBridge`) from these two, so the only
remaining mathematical obligation of the whole Artin development is
`Theory.RCF.HasQuantifierElimination` — the Tarski–Seidenberg core, provable via Sturm's theorem.
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

/-- A ring hom that preserves and reflects `≤` is an `orderedRing`-embedding. -/
def ringOrderEmbedding {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C]
    (ψ : ℝ →+* C) (hle : ∀ a b, ψ a ≤ ψ b ↔ a ≤ b) : ℝ ↪[orderedRing] C where
  toFun := ψ
  inj' := ψ.injective
  map_fun' := by
    rintro n (rf | ef) x
    · cases rf <;> simp [map_add, map_mul, map_neg]
    · exact ef.elim
  map_rel' := by
    rintro n (er | or) x
    · exact er.elim
    · cases or
      exact hle (x 0) (x 1)

/-- **From quantifier elimination, an ordered-ring embedding of `ℝ` is elementary.** Let `T` be an
`orderedRing`-theory modelled by both `ℝ` and an extension `C`, and suppose `T` has quantifier
elimination. Then the embedding `g : ℝ ↪[orderedRing] C` preserves *and* reflects the realization of
**every** formula: a quantified formula is `T`-equivalent to a quantifier-free one
(`hqe`), and quantifier-free formulas are absolute along embeddings (`IsQF.realize_embedding`). This
is precisely the model-completeness content, reduced to the QE hypothesis on `T`. -/
theorem realize_transfer_of_qe {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C]
    (g : ℝ ↪[orderedRing] C) (T : orderedRing.Theory) [ℝ ⊨ T] [C ⊨ T]
    (hqe : T.HasQuantifierElimination) {m : ℕ} (χ : orderedRing.BoundedFormula Empty m)
    (w : Fin m → ℝ) :
    χ.Realize (default : Empty → C) (g ∘ w) ↔ χ.Realize (default : Empty → ℝ) w := by
  haveI : Nonempty C := ⟨0⟩
  haveI : Nonempty ℝ := ⟨0⟩
  obtain ⟨Θ, hΘqf, hΘeq⟩ := hqe χ.toFormula
  have hg : (Sum.elim (default : Empty → C) (g ∘ w)) = g ∘ Sum.elim default w := by
    funext z; rcases z with e | i
    · exact e.elim
    · rfl
  have hemb : Θ.Realize (g ∘ Sum.elim (default : Empty → ℝ) w)
      ↔ Θ.Realize (Sum.elim default w) := by
    have e : (g ∘ (default : Fin 0 → ℝ)) = (default : Fin 0 → C) := funext fun i => i.elim0
    have h := hΘqf.realize_embedding g (v := Sum.elim (default : Empty → ℝ) w) (xs := default)
    rw [e] at h
    simpa only [Formula.boundedFormula_realize_eq_realize] using h
  calc χ.Realize (default : Empty → C) (g ∘ w)
      ↔ χ.toFormula.Realize (Sum.elim default (g ∘ w)) :=
        (BoundedFormula.realize_toFormula χ (Sum.elim default (g ∘ w))).symm
    _ ↔ Θ.Realize (Sum.elim default (g ∘ w)) := hΘeq.realize_iff
    _ ↔ Θ.Realize (g ∘ Sum.elim default w) := by rw [hg]
    _ ↔ Θ.Realize (Sum.elim default w) := hemb
    _ ↔ χ.toFormula.Realize (Sum.elim default w) := hΘeq.realize_iff.symm
    _ ↔ χ.Realize (default : Empty → ℝ) w :=
        BoundedFormula.realize_toFormula χ (Sum.elim default w)

/-- **Model completeness of real closed fields.** Every real closed field `C` with a ring embedding
`ψ` of `ℝ` receives `ℝ` as an *elementary* substructure in the language of ordered rings, and the
elementary embedding's underlying map is `ψ`.

Reduced, via the Tarski–Vaught test `Embedding.toElementaryEmbedding` and `realize_transfer_of_qe`,
to **quantifier elimination for `T`** (`hqe`), where `T` is any `orderedRing`-theory modelled by
both `ℝ` and `C` (e.g. `Theory.RCF`). That is the genuinely deep Tarski–Seidenberg ingredient. -/
theorem realClosed_elementaryEmbedding
    (C : Type*) [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]
    (ψ : ℝ →+* C) (T : orderedRing.Theory) [ℝ ⊨ T] [C ⊨ T]
    (hqe : T.HasQuantifierElimination) :
    ∃ g : ℝ ↪ₑ[orderedRing] C, ∀ r, g r = ψ r := by
  -- A ring hom out of `ℝ` is an order embedding: it preserves nonnegativity (every nonnegative real
  -- is a square) and reflects it (by injectivity).
  have hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ψ x := fun x hx => by
    rw [show x = Real.sqrt x * Real.sqrt x from (Real.mul_self_sqrt hx).symm, map_mul]
    exact mul_self_nonneg _
  have h0 : ∀ y : ℝ, 0 ≤ ψ y ↔ 0 ≤ y := fun y =>
    ⟨fun hy => not_lt.1 fun hy' => by
      have h1 := hnn _ (neg_nonneg.2 hy'.le)
      rw [map_neg] at h1
      have hz : ψ y = 0 := le_antisymm (by linarith) hy
      exact hy'.ne (ψ.injective (by rw [hz, map_zero])), hnn y⟩
  have hle : ∀ a b, ψ a ≤ ψ b ↔ a ≤ b := fun a b =>
    calc ψ a ≤ ψ b ↔ 0 ≤ ψ b - ψ a := sub_nonneg.symm
      _ ↔ 0 ≤ ψ (b - a) := by rw [map_sub]
      _ ↔ 0 ≤ b - a := h0 (b - a)
      _ ↔ a ≤ b := sub_nonneg
  refine ⟨(ringOrderEmbedding ψ hle).toElementaryEmbedding ?_, fun _ => rfl⟩
  -- **RCF back-and-forth via quantifier elimination.** Tarski–Vaught test: an existential witness
  -- in `C` over `ℝ`-parameters descends to `ℝ`. The witness `a` may be transcendental over `ℝ`, but
  -- QE (`realize_transfer_of_qe`) makes the embedding elementary, so realization transfers freely.
  set g := ringOrderEmbedding ψ hle with hg
  intro n φ x a hφa
  -- Reflect the *existence* of a witness from `C` down to `ℝ`.
  have hex : (φ.ex).Realize (default : Empty → C) (g ∘ x) :=
    BoundedFormula.realize_ex.mpr ⟨a, hφa⟩
  rw [realize_transfer_of_qe g T hqe, BoundedFormula.realize_ex] at hex
  obtain ⟨b, hb⟩ := hex
  -- Push the real witness `b` back up into `C`.
  refine ⟨b, ?_⟩
  have hpush := (realize_transfer_of_qe g T hqe φ (Fin.snoc x b)).mpr hb
  rwa [Fin.comp_snoc] at hpush

/-! The eval↔formula bridge and the assembled transfer `exists_neg_eval_of_real_closed` are proved
in `Mathlib.NumberTheory.Transcendental.ArtinBridge`, which has the free-commutative-ring encoding
machinery. Nothing here is a `sorry`; the whole development is parameterized by the hypothesis
`Theory.RCF.HasQuantifierElimination`. -/

end Artin.ModelTheory
