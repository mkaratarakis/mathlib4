/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.RingTheory.FreeCommRing
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing

/-!
# Term ↔ polynomial dictionary for one-variable quantifier elimination

The one-quantifier step of quantifier elimination for real closed fields (`RCF_ex_isQFEquivalent` in
`ArtinQE`) works with a single bound variable. Its atomic subformulas are ring (in)equalities
`t₁ = t₂`, `t₁ ≤ t₂` whose terms live in the parameters `α` with one bound variable, encoded as
`FreeCommRing (α ⊕ Fin 1)` (the free-commutative-ring encoding used by `ArtinBridge`).

This file provides the bridge to univariate polynomials: `toPoly` views such a term as a polynomial
over `FreeCommRing α` (the extra variable becomes `X`, the parameters become constant coefficients),
and `lift_eq_eval_toPoly` says that realizing the term — assigning `v : α → M` to the parameters and
`x : M` to the bound variable — equals evaluating that polynomial (with coefficients pushed into `M`
via `v`) at `x`. This is the key that turns each atom into a polynomial sign condition `P(x) ⋛ 0`
whose coefficients are terms in the parameters.
-/

open Polynomial

namespace Artin.ModelTheory

variable {α : Type*}

/-- View a free-commutative-ring element in variables `α ⊕ Fin 1` as a univariate polynomial over
`FreeCommRing α`: the `Fin 1` variable becomes `X`, each parameter `a : α` becomes the constant
`C (of a)`. -/
noncomputable def toPoly : FreeCommRing (α ⊕ Fin 1) →+* Polynomial (FreeCommRing α) :=
  FreeCommRing.lift (Sum.elim (fun a => C (FreeCommRing.of a)) (fun _ => X))

@[simp] theorem toPoly_of_inl (a : α) :
    toPoly (FreeCommRing.of (Sum.inl a)) = C (FreeCommRing.of a) := by
  simp [toPoly]

@[simp] theorem toPoly_of_inr (i : Fin 1) :
    toPoly (FreeCommRing.of (Sum.inr i)) = (X : Polynomial (FreeCommRing α)) := by
  simp [toPoly]

/-- **Realization dictionary.** Realizing a free-commutative-ring term with parameters `v : α → M`
and bound value `x : M` equals evaluating the associated polynomial (coefficients pushed to `M` via
`v`) at `x`. -/
theorem lift_eq_eval_toPoly {M : Type*} [CommRing M] (v : α → M) (x : M)
    (t : FreeCommRing (α ⊕ Fin 1)) :
    FreeCommRing.lift (Sum.elim v (fun _ => x)) t
      = Polynomial.eval₂ (FreeCommRing.lift v) x (toPoly t) := by
  have h : (FreeCommRing.lift (Sum.elim v (fun _ => x)) : FreeCommRing (α ⊕ Fin 1) →+* M)
      = (Polynomial.eval₂RingHom (FreeCommRing.lift v) x).comp toPoly := by
    refine FreeCommRing.hom_ext (fun z => ?_)
    rcases z with a | i
    · simp
    · fin_cases i; simp
  exact DFunLike.congr_fun h t

open FirstOrder Language

/-- The univariate polynomial (over `FreeCommRing α`) associated to a *ring term* in one bound
variable: realize the term in the free commutative ring (variables ↦ generators), then view it as a
polynomial via `toPoly`. -/
noncomputable def atomPoly (t : Language.ring.Term (α ⊕ Fin 1)) : Polynomial (FreeCommRing α) :=
  letI : Ring.CompatibleRing (FreeCommRing (α ⊕ Fin 1)) := Ring.compatibleRingOfRing _
  toPoly (t.realize FreeCommRing.of)

/-- **Atom dictionary.** In any compatible commutative ring, realizing a ring term with parameters
`v : α → M` and bound value `x` equals evaluating its associated polynomial `atomPoly t`
(coefficients pushed to `M` via `v`) at `x`. -/
theorem ring_term_realize_eq_eval {M : Type*} [CommRing M] [Ring.CompatibleRing M]
    (v : α → M) (x : M) (t : Language.ring.Term (α ⊕ Fin 1)) :
    t.realize (Sum.elim v (fun _ => x))
      = Polynomial.eval₂ (FreeCommRing.lift v) x (atomPoly t) := by
  letI : Ring.CompatibleRing (FreeCommRing (α ⊕ Fin 1)) := Ring.compatibleRingOfRing _
  rw [atomPoly, ← lift_eq_eval_toPoly]
  -- Reduce to naturality: `t.realize w = lift w (t.realize of)`, by induction on the term.
  induction t with
  | var a => simp
  | func f a ih => cases f <;> simp [ih]

/-- **Equality atom as a sign condition.** An equality of ring terms in one bound variable becomes
`P(x) = 0` for `P` the difference of the associated polynomials. -/
theorem realize_eq_iff {M : Type*} [CommRing M] [Ring.CompatibleRing M]
    (v : α → M) (x : M) (t₁ t₂ : Language.ring.Term (α ⊕ Fin 1)) :
    (t₁.realize (Sum.elim v (fun _ => x)) = t₂.realize (Sum.elim v (fun _ => x)))
      ↔ Polynomial.eval₂ (FreeCommRing.lift v) x (atomPoly t₁ - atomPoly t₂) = 0 := by
  rw [ring_term_realize_eq_eval v x t₁, ring_term_realize_eq_eval v x t₂,
    Polynomial.eval₂_sub, sub_eq_zero]

/-- **Order atom as a sign condition.** An inequality of ring terms in one bound variable becomes
`0 ≤ P(x)` for `P` the difference of the associated polynomials. -/
theorem realize_le_iff {M : Type*} [CommRing M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : α → M) (x : M) (t₁ t₂ : Language.ring.Term (α ⊕ Fin 1)) :
    (t₁.realize (Sum.elim v (fun _ => x)) ≤ t₂.realize (Sum.elim v (fun _ => x)))
      ↔ 0 ≤ Polynomial.eval₂ (FreeCommRing.lift v) x (atomPoly t₂ - atomPoly t₁) := by
  rw [ring_term_realize_eq_eval v x t₁, ring_term_realize_eq_eval v x t₂,
    Polynomial.eval₂_sub, sub_nonneg]

end Artin.ModelTheory
