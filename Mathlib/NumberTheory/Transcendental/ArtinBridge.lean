/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.RingTheory.FreeCommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
import Mathlib.NumberTheory.Transcendental.ArtinTransfer
import Mathlib.NumberTheory.Transcendental.ArtinRCF
import Mathlib.NumberTheory.Transcendental.ArtinRealClosure

/-!
# Algebra core of the Artin eval↔formula bridge

To encode `∃ x, f(x) < 0` (for `f : MvPolynomial σ ℝ`) as a first-order formula over the language of
ordered rings — with the real coefficients of `f` as parameters — one first represents `f` as an
element `Artin.ModelTheory.polyFree f` of the free commutative ring over `ℝ ⊕ σ`, using a generator
`inl r` for each real coefficient `r` and `inr i` for each indeterminate `i`.

`lift_polyFree` shows the key fact: lifting `polyFree f` along a coefficient ring hom `c` and a
point `x` recovers `MvPolynomial.eval₂ c x f`. Composing with `FirstOrder.Ring.termOfFreeCommRing`
(whose
realization is exactly `FreeCommRing.lift`) turns `polyFree f` into an ordered-ring term whose
realization is the polynomial value. Wrapping that in `∃ point, · < 0` (`formulaOfPoly`) and
transporting realization along `ElementaryEmbedding.map_formula` gives the full `bridge`, which
reflects `∃ x, f(x) < 0` from a real closed extension back to `ℝ`.
-/

open MvPolynomial FirstOrder Language

namespace Artin.ModelTheory

variable {σ : Type*}

/-- `f` as an element of the free commutative ring over `ℝ ⊕ σ`: a generator `inl r` for each real
coefficient `r`, and `inr i` for each indeterminate `i`. -/
noncomputable def polyFree (f : MvPolynomial σ ℝ) : FreeCommRing (ℝ ⊕ σ) :=
  f.support.sum fun m =>
    FreeCommRing.of (Sum.inl (f.coeff m)) * m.prod fun i k => FreeCommRing.of (Sum.inr i) ^ k

/-- Lifting `polyFree f` with the coefficient ring hom `c` on the `inl` generators and the point `x`
on the `inr` generators recovers `eval₂ c x f`. -/
theorem lift_polyFree {M : Type*} [CommRing M] (c : ℝ →+* M) (x : σ → M) (f : MvPolynomial σ ℝ) :
    FreeCommRing.lift (Sum.elim (fun r => c r) x) (polyFree f) = eval₂ c x f := by
  simp only [polyFree, eval₂_eq, map_sum, map_mul, FreeCommRing.lift_of, Sum.elim_inl,
    Finsupp.prod, map_prod, map_pow, Sum.elim_inr]

/-- The ordered-ring term for `f` (the free-commutative-ring encoding pushed through
`termOfFreeCommRing` into the language of ordered rings) realizes to the polynomial value. -/
theorem realize_termPolyFree {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (c : ℝ →+* M) (x : σ → M) (f : MvPolynomial σ ℝ) :
    Term.realize (Sum.elim (fun r => c r) x)
      ((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm (Ring.termOfFreeCommRing (polyFree f)))
      = eval₂ c x f := by
  rw [LHom.realize_onTerm, Ring.realize_termOfFreeCommRing, lift_polyFree]

/-- The ordered-ring formula `∃ (point), f(point) < 0`, with the coefficients of `f` (elements of
`ℝ`) as free variables. -/
noncomputable def formulaOfPoly [Finite σ] (f : MvPolynomial σ ℝ) : orderedRing.Formula ℝ :=
  Formula.iExs σ (Term.lt
    (Term.relabel (Sum.inl : (ℝ ⊕ σ) → (ℝ ⊕ σ) ⊕ Fin 0)
      ((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm
        (Ring.termOfFreeCommRing (polyFree f))))
    (Term.relabel (Sum.inl : (ℝ ⊕ σ) → (ℝ ⊕ σ) ⊕ Fin 0)
      ((LHom.sumInl : Language.ring →ᴸ orderedRing).onTerm 0)))

/-- `formulaOfPoly f`, realized with the coefficient assignment `c` (a ring hom), holds iff `f` is
negative somewhere. -/
theorem realize_formulaOfPoly [Finite σ] {M : Type*} [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] (c : ℝ →+* M) (f : MvPolynomial σ ℝ) :
    (formulaOfPoly f).Realize (fun r => c r) ↔ ∃ i : σ → M, eval₂ c i f < 0 := by
  rw [formulaOfPoly, Formula.realize_iExs]
  refine exists_congr fun i => ?_
  simp only [Formula.Realize, Term.realize_lt, Term.realize_relabel, Sum.elim_comp_inl,
    LHom.realize_onTerm, Ring.realize_termOfFreeCommRing, lift_polyFree, Ring.realize_zero]

/-- **The eval↔formula bridge.** An elementary embedding `g : ℝ ↪ₑ C` whose underlying map is the
ring hom `ψ` reflects the existential inequality `∃ x, f(x) < 0`: negativity of `f` somewhere in `C`
(through `ψ`) descends to negativity somewhere in `ℝ`. Proved by realizing `formulaOfPoly f` in `C`
at `⇑g = ψ`, transporting it to `ℝ` by `ElementaryEmbedding.map_formula`, and reading off the real
witness. -/
theorem bridge [Finite σ] {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C]
    (g : ℝ ↪ₑ[orderedRing] C) (ψ : ℝ →+* C) (hg : ∀ r, g r = ψ r)
    (ξ : σ → C) (f : MvPolynomial σ ℝ) (h : eval₂ ψ ξ f < 0) :
    ∃ a : σ → ℝ, eval a f < 0 := by
  have hC : (formulaOfPoly f).Realize (fun r => (g : ℝ → C) r) := by
    rw [show (fun r => (g : ℝ → C) r) = (fun r => ψ r) from funext hg, realize_formulaOfPoly]
    exact ⟨ξ, h⟩
  have hR := (g.map_formula (formulaOfPoly f) (fun r => (RingHom.id ℝ) r)).mp hC
  rw [realize_formulaOfPoly] at hR
  obtain ⟨a, ha⟩ := hR
  exact ⟨a, by simpa using ha⟩

/-- **The Tarski transfer for Artin's theorem**, assembled from RCF model completeness
(`realClosed_elementaryEmbedding`) and the eval↔formula `bridge`: a polynomial inequality solvable
in a real closed field `C ⊇ ℝ` is solvable in `ℝ`. The one remaining hypothesis is quantifier
elimination for `Theory.RCF` (`hqe`) — the Tarski–Seidenberg core, provable via Sturm's theorem. -/
theorem exists_neg_eval_of_real_closed [Finite σ]
    (C : Type*) [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]
    (hqe : Theory.RCF.HasQuantifierElimination)
    (ψ : ℝ →+* C) (ξ : σ → C) (f : MvPolynomial σ ℝ) (h : eval₂ ψ ξ f < 0) :
    ∃ a : σ → ℝ, eval a f < 0 := by
  obtain ⟨g, hg⟩ := realClosed_elementaryEmbedding C ψ Theory.RCF hqe
  exact bridge g ψ hg ξ f h

end Artin.ModelTheory
