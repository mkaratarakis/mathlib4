/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Transfer
import Mathlib.NumberTheory.Transcendental.ArtinQEDict
import Mathlib.NumberTheory.Transcendental.ArtinTransfer

/-!
# Semantic one-existential transfer for real closed fields

The remaining obligation of the Artin development is `RCF_ex_isQFEquivalent` (`ArtinQE`): the
existential closure of a quantifier-free formula in one bound variable is `Theory.RCF`-equivalent
to a quantifier-free formula. This file proves its **semantic content**, sorry-free:

* `realize_ex_map_iff` — for a quantifier-free `θ` in one bound variable with parameters in a real
  closed field `K` and any real closed extension `φ : K →+* L`, the existential `∃ x, θ` holds in
  `L` iff it holds in `K`.

The proof composes the two dictionaries built earlier:

1. every atom of `θ` is a polynomial sign condition, with the atom polynomials collected by
   `atomPolys` (via `ArtinQEDict.atomPoly`, `realize_eq_iff`, `realize_le_iff`); the truth value of
   `θ` at a point is a function of the sign vector of `atomPolys θ` at that point
   (`realize_iff_realize_of_sgn_eq`);
2. the realizable sign vectors of a finite polynomial family are the same in `K` and in `L`
   (`Sturm.exists_sgn_eval_map_iff` — Tarski transfer in one variable, powered by Sturm's theorem).

What remains for `RCF_ex_isQFEquivalent` beyond this file is purely syntactic: *constructing* a
quantifier-free formula over the parameters expressing the realizability condition, uniformly in
the parameters.
-/

open FirstOrder Language Polynomial Sturm

namespace Artin.ModelTheory

variable {α β : Type*}

/-! ### Ordered-ring terms are ring terms

`Language.order` has no function symbols, so every term of `orderedRing = ring.sum order` is
built from ring functions only. -/

/-- Convert an `orderedRing`-term to a `ring`-term (the order language contributes no function
symbols). -/
def toRingTerm : orderedRing.Term β → Language.ring.Term β
  | .var b => .var b
  | .func (Sum.inl g) ts => .func g (fun i => toRingTerm (ts i))
  | .func (Sum.inr g) _ => g.elim

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- Realization is unchanged by `toRingTerm`: the sum structure interprets ring function symbols
by the ring operations. -/
theorem realize_toRingTerm (w : β → K) (t : orderedRing.Term β) :
    (toRingTerm t).realize w = t.realize w := by
  induction t with
  | var b => rfl
  | func f ts ih =>
    rcases f with g | g
    · simp only [toRingTerm, Term.realize_func, funMap_sumInl]
      exact congrArg _ (funext fun i => ih i)
    · exact g.elim

/-! ### The atom polynomials of a quantifier-free formula -/

/-- The list of atom polynomials of a formula in one bound variable: each atom `t₁ = t₂` or
`t₁ ≤ t₂` contributes the difference of the polynomials associated to its two terms. The truth
value of a quantifier-free formula at a point is a function of the signs of these polynomials
there (`realize_iff_realize_of_sgn_eq`). -/
noncomputable def atomPolys : orderedRing.BoundedFormula α 1 → List (Polynomial (FreeCommRing α))
  | .falsum => []
  | .equal t₁ t₂ => [atomPoly (toRingTerm t₁) - atomPoly (toRingTerm t₂)]
  | .rel (Sum.inl r) _ => r.elim
  | .rel (Sum.inr .le) ts => [atomPoly (toRingTerm (ts 1)) - atomPoly (toRingTerm (ts 0))]
  | .imp θ₁ θ₂ => atomPolys θ₁ ++ atomPolys θ₂
  | .all _ => []

private theorem atomPolys_equal (t₁ t₂ : orderedRing.Term (α ⊕ Fin 1)) :
    atomPolys (t₁.bdEqual t₂) = [atomPoly (toRingTerm t₁) - atomPoly (toRingTerm t₂)] := by
  rw [Term.bdEqual, atomPolys]

private theorem atomPolys_le (ts : Fin 2 → orderedRing.Term (α ⊕ Fin 1)) :
    atomPolys (Relations.boundedFormula (Sum.inr .le) ts)
      = [atomPoly (toRingTerm (ts 1)) - atomPoly (toRingTerm (ts 0))] := by
  rw [Relations.boundedFormula, atomPolys]

private theorem atomPolys_imp (θ₁ θ₂ : orderedRing.BoundedFormula α 1) :
    atomPolys (θ₁.imp θ₂) = atomPolys θ₁ ++ atomPolys θ₂ := by
  rw [atomPolys]

/-! ### Sign helper lemmas -/

omit [IsStrictOrderedRing K] in
private theorem sgn_eq_zero_iff {k : K} : sgn k = 0 ↔ k = 0 := by
  unfold sgn
  split_ifs with h1 h2
  · exact iff_of_false (by norm_num) (by rintro rfl; exact lt_irrefl _ h1)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by norm_num) h2

omit [IsStrictOrderedRing K] in
private theorem sgn_ne_neg_one_iff {k : K} : sgn k ≠ -1 ↔ 0 ≤ k := by
  unfold sgn
  split_ifs with h1 h2
  · exact iff_of_true (by norm_num) h1.le
  · exact iff_of_true (by norm_num) (le_of_eq h2.symm)
  · exact iff_of_false (by simp) fun h => h2 (le_antisymm (not_lt.mp h1) h)

private theorem forall_of_map_eq {γ δ : Type*} {l : List γ} {f g : γ → δ}
    (h : l.map f = l.map g) : ∀ b ∈ l, f b = g b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact h.1
    · exact ih h.2 b hb'

/-! ### Term evaluation dictionaries, specialized to the two fields -/

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
private theorem lift_comp (φ : K →+* L) (v : α → K) :
    (FreeCommRing.lift (fun a => φ (v a))) = φ.comp (FreeCommRing.lift v) :=
  FreeCommRing.hom_ext fun a => by simp

/-- Realizing an ordered-ring term in `K` is evaluating its atom polynomial (coefficients pushed
into `K`). -/
private theorem term_eval_K (v : α → K) (x : K) (t : orderedRing.Term (α ⊕ Fin 1)) :
    t.realize (Sum.elim v fun _ => x)
      = ((atomPoly (toRingTerm t)).map (FreeCommRing.lift v)).eval x := by
  rw [← realize_toRingTerm, ring_term_realize_eq_eval, Polynomial.eval_map]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Realizing an ordered-ring term in `L` with parameters pushed through `φ` is evaluating the
`φ`-image of the same `K`-coefficient polynomial. -/
private theorem term_eval_L (φ : K →+* L) (v : α → K) (y : L)
    (t : orderedRing.Term (α ⊕ Fin 1)) :
    t.realize (Sum.elim (fun a => φ (v a)) fun _ => y)
      = (((atomPoly (toRingTerm t)).map (FreeCommRing.lift v)).map φ).eval y := by
  rw [← realize_toRingTerm, ring_term_realize_eq_eval, Polynomial.map_map, ← lift_comp φ v,
    Polynomial.eval_map]

/-! ### Truth is a function of the sign vector -/

/-- **Truth from signs.** If a point `x : K` and a point `y : L` produce the same sign vector on
the atom polynomials of a quantifier-free `θ` (coefficients pushed forward along `φ` on the `L`
side), then `θ` holds at `x` in `K` iff it holds at `y` in `L`. -/
theorem realize_iff_realize_of_sgn_eq (φ : K →+* L) (v : α → K)
    {θ : orderedRing.BoundedFormula α 1} (hθ : θ.IsQF) (x : K) (y : L) :
    (∀ p ∈ atomPolys θ,
      sgn ((p.map (FreeCommRing.lift v)).eval x)
        = sgn (((p.map (FreeCommRing.lift v)).map φ).eval y)) →
    (θ.Realize v (fun _ => x) ↔ θ.Realize (fun a => φ (v a)) (fun _ => y)) := by
  induction hθ with
  | falsum => exact fun _ => Iff.rfl
  | of_isAtomic h =>
    intro hsgn
    cases h with
    | equal t₁ t₂ =>
      have hp := hsgn (atomPoly (toRingTerm t₁) - atomPoly (toRingTerm t₂))
        (by rw [atomPolys_equal]; exact List.mem_singleton_self _)
      simp only [Polynomial.map_sub, Polynomial.eval_sub] at hp
      change t₁.realize _ = t₂.realize _ ↔ t₁.realize _ = t₂.realize _
      rw [term_eval_K v x t₁, term_eval_K v x t₂, term_eval_L φ v y t₁, term_eval_L φ v y t₂]
      simp only [← sub_eq_zero (b := (((atomPoly (toRingTerm t₂)).map _).map _).eval y),
        ← sub_eq_zero (b := ((atomPoly (toRingTerm t₂)).map _).eval x)]
      rw [← sgn_eq_zero_iff, ← sgn_eq_zero_iff (K := L), hp]
    | rel R ts =>
      rcases R with r | r
      · exact r.elim
      cases r
      have hp := hsgn (atomPoly (toRingTerm (ts 1)) - atomPoly (toRingTerm (ts 0)))
        (by rw [atomPolys_le]; exact List.mem_singleton_self _)
      simp only [Polynomial.map_sub, Polynomial.eval_sub] at hp
      change (ts 0).realize _ ≤ (ts 1).realize _ ↔ (ts 0).realize _ ≤ (ts 1).realize _
      rw [term_eval_K v x (ts 0), term_eval_K v x (ts 1), term_eval_L φ v y (ts 0),
        term_eval_L φ v y (ts 1), ← sub_nonneg,
        ← sub_nonneg (a := (((atomPoly (toRingTerm (ts 1))).map _).map _).eval y),
        ← sgn_ne_neg_one_iff, ← sgn_ne_neg_one_iff (K := L), hp]
  | imp h₁ h₂ ih₁ ih₂ =>
    intro hsgn
    simp only [BoundedFormula.realize_imp]
    rw [ih₁ (fun p hp => hsgn p (by rw [atomPolys_imp]; exact List.mem_append.mpr (Or.inl hp))),
      ih₂ (fun p hp => hsgn p (by rw [atomPolys_imp]; exact List.mem_append.mpr (Or.inr hp)))]

/-! ### The semantic one-existential transfer -/

/-- `Fin.snoc` into an empty tuple is the constant tuple. -/
private theorem snoc_elim0_eq {M : Type*} (a : M) :
    (Fin.snoc Fin.elim0 a : Fin 1 → M) = fun _ => a := by
  funext i
  fin_cases i
  simp [Fin.snoc]

/-- **Semantic one-existential transfer for real closed fields.** For a quantifier-free formula
`θ` in one bound variable over the language of ordered rings, with parameters `v` in a real closed
field `K` and any real closed extension `φ : K →+* L`: the existential `θ.ex` holds in `L` (with
parameters `φ ∘ v`) iff it holds in `K`.

This is the semantic content of the one-quantifier elimination step `RCF_ex_isQFEquivalent`: the
witness in `L` is converted into a witness in `K` by Tarski transfer of the realizable sign
vectors of the atom polynomials (`Sturm.exists_sgn_eval_map_iff`). -/
theorem realize_ex_map_iff [IsRealClosed K] [IsRealClosed L] (φ : K →+* L) (v : α → K)
    {θ : orderedRing.BoundedFormula α 1} (hθ : θ.IsQF) :
    θ.ex.Realize (fun a => φ (v a)) Fin.elim0 ↔ θ.ex.Realize v Fin.elim0 := by
  simp only [BoundedFormula.realize_ex, snoc_elim0_eq]
  set ps : List K[X] := (atomPolys θ).map (Polynomial.map (FreeCommRing.lift v)) with hps
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := (exists_sgn_eval_map_iff φ ps
      (ps.map (fun p => sgn ((p.map φ).eval y)))).mp ⟨y, rfl⟩
    have hsgn : ∀ p ∈ atomPolys θ,
        sgn ((p.map (FreeCommRing.lift v)).eval x)
          = sgn (((p.map (FreeCommRing.lift v)).map φ).eval y) := fun p hp =>
      forall_of_map_eq hx _ (List.mem_map_of_mem hp)
    exact ⟨x, (realize_iff_realize_of_sgn_eq φ v hθ x y hsgn).mpr hy⟩
  · rintro ⟨x, hx⟩
    have hsgn : ∀ p ∈ atomPolys θ,
        sgn ((p.map (FreeCommRing.lift v)).eval x)
          = sgn (((p.map (FreeCommRing.lift v)).map φ).eval (φ x)) := fun p _ => by
      rw [Sturm.eval_map_apply, sgn_map]
    exact ⟨φ x, (realize_iff_realize_of_sgn_eq φ v hθ x (φ x) hsgn).mp hx⟩

end Artin.ModelTheory
