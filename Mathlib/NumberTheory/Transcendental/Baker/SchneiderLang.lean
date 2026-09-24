/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Transcendental.Baker.CriterionMain
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# The criterion of Schneider–Lang for `ℂ^{d₀} × (ℂˣ)^{d₁}`

This file states the form of the Schneider–Lang criterion from which Baker's theorem is
deduced in Chapter 4 of [waldschmidt2000], together with the two special cases used
there.  The criterion itself (Theorem 4.1 of [waldschmidt2000]) concerns algebraic values
of algebraically independent entire functions satisfying differential equations; only the
corollary for products of additive and multiplicative groups is needed, and that is what
is stated here.

Throughout, `L` denotes the `ℚ`-vector space of logarithms of nonzero algebraic numbers,
written `x ∈ L` as `IsAlgebraic ℚ (Complex.exp x)`; `exp x ≠ 0` is automatic, so no
nonvanishing hypothesis is needed.  For `x y : Fin n → ℂ` the pairing `x · y` of the book
is the sum `∑ v, x v * y v`.

## Main statements

* `Transcendental.schneiderLang`: **Corollary 4.2** of [waldschmidt2000].  Given
  `d₀ ≤ n < d₀ + d₁`, `ℚ`-linearly independent `x 1, …, x d₁` in `ℂⁿ` with algebraic
  coordinates, and a basis `y 1, …, y n` of `ℂⁿ` over `ℂ`, one of the `(d₀ + d₁) * n`
  numbers `y j h`
  (`h < d₀`) and `exp (x i · y j)` is transcendental.
* `Transcendental.schneiderLang_zero`: **Corollary 4.3**, the case `d₀ = 0`, phrased as
  in the book with a family of rank at least `n + 1` and a spanning family of `ℂⁿ`.
* `Transcendental.schneiderLang_one`: **Corollary 4.4**, the case `d₀ = 1`, `d₁ = n = d`.

`schneiderLang_zero` yields the homogeneous case of Baker's theorem and
`schneiderLang_one` the nonhomogeneous case; both deductions are in
`Mathlib/NumberTheory/Transcendental/Baker/Reduction.lean`.

## The proof

`schneiderLang` is proved in §§4.3-4.6 of [waldschmidt2000], formalized across this directory:

* **§4.3, Proposition 4.7** (Schwarz's lemma for Cartesian products):
  `MultiIndex.norm_le_of_taylorCoeff_eq_zero` in
  `Mathlib/NumberTheory/Transcendental/Baker/SchwarzProduct.lean`, by Newton division one
  coordinate at a time in place of the ideal-theoretic Lemma 4.8.
* **§4.4, Lemma 4.9** (Taylor coefficients of `z ^ τ exp (w · z)`):
  `MultiIndex.taylorCoeff_expMonomial` in `Mathlib/NumberTheory/Transcendental/Baker/ExpPoly.lean`.
* **§4.5, Proposition 4.10** (the auxiliary function), from Lemmas 4.11-4.13:
  `ThueSiegel.exists_auxiliary_function` in
  `Mathlib/NumberTheory/Transcendental/Baker/AuxiliaryFunction.lean`.
* **§4.6** (the transcendence argument): `Transcendental.SchneiderLangProof.core` in
  `Mathlib/NumberTheory/Transcendental/Baker/Criterion.lean`, with the choice of parameters and the
  conclusion `Transcendental.SchneiderLangProof.main` in
  `Mathlib/NumberTheory/Transcendental/Baker/CriterionMain.lean`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic
  Groups*][waldschmidt2000], Chapter 4
-/

@[expose] public section

open Complex Finset

namespace Transcendental

variable {n d₀ d₁ : ℕ}

/-- **Corollary 4.2** of [waldschmidt2000] (criterion of Schneider–Lang for
`ℂ^{d₀} × (ℂˣ)^{d₁}`).

Let `d₀ ≤ n < d₀ + d₁`, let `x 1, …, x d₁` be `ℚ`-linearly independent vectors with
algebraic coordinates, and let `y 1, …, y n` be a basis of `ℂⁿ` over `ℂ`.  Then one at
least of the `(d₀ + d₁) * n` numbers `y j h` (for `h < d₀`) and `exp (x i · y j)` is
transcendental.

The proof, which occupies §§4.3–4.6 of [waldschmidt2000], constructs an auxiliary
function by Thue–Siegel's lemma and applies a Schwarz lemma for Cartesian products. -/
theorem schneiderLang (hd₀ : d₀ ≤ n) (hn : n < d₀ + d₁)
    (x : Fin d₁ → Fin n → ℂ) (hx : ∀ i v, IsAlgebraic ℚ (x i v))
    (hxli : LinearIndependent ℚ x)
    (y : Fin n → Fin n → ℂ) (hyli : LinearIndependent ℂ y) :
    (∃ (h : Fin d₀) (j : Fin n), Transcendental ℚ (y j (Fin.castLE hd₀ h))) ∨
      ∃ (i : Fin d₁) (j : Fin n), Transcendental ℚ (exp (∑ v, x i v * y j v)) :=
  SchneiderLangProof.main hd₀ hn x hx hxli y hyli

/-- **Corollary 4.3** of [waldschmidt2000]: the case `d₀ = 0` of `schneiderLang`.

If `x 1, …, x d` have algebraic coordinates and are `ℚ`-linearly independent with
`n + 1 ≤ d`, and if `y 1, …, y l` span `ℂⁿ` over `ℂ`, then one at least of the `d * l`
numbers `x i · y j` is not a logarithm of an algebraic number.

For `n = 1` this is the theorem of Gel'fond–Schneider.  The book states the hypothesis on
the `x i` as "they generate a subgroup of rank at least `n + 1`"; the form used here is
what the proof of Theorem 4.5 supplies. -/
theorem schneiderLang_zero {d l : ℕ} (hd : n + 1 ≤ d) (x : Fin d → Fin n → ℂ)
    (hx : ∀ i v, IsAlgebraic ℚ (x i v)) (hxli : LinearIndependent ℚ x)
    (y : Fin l → Fin n → ℂ) (hy : Submodule.span ℂ (Set.range y) = ⊤) :
    ∃ (i : Fin d) (j : Fin l), ¬ IsAlgebraic ℚ (exp (∑ v, x i v * y j v)) := by
  -- Extract from `y` a subfamily which is a basis of `ℂⁿ`.
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ y
  rw [hy] at hspan
  let B : Module.Basis κ ℂ (Fin n → ℂ) := Module.Basis.mk hli hspan.ge
  have : Fintype κ := IsNoetherian.fintypeBasisIndex B
  have hcard : Fintype.card κ = n := by
    have h := Module.finrank_eq_card_basis B
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  -- Keep `n + 1` of the `x i`; a restriction along an injection stays independent.
  have hx'li : LinearIndependent ℚ (x ∘ Fin.castLE hd) := hxli.comp _ (Fin.castLE_injective hd)
  have hy'li : LinearIndependent ℂ ((y ∘ a) ∘ e) := hli.comp e e.injective
  rcases schneiderLang (Nat.zero_le n) (by omega) (x ∘ Fin.castLE hd)
      (fun i v => hx _ v) hx'li ((y ∘ a) ∘ e) hy'li with ⟨h, -, -⟩ | ⟨i, j, hij⟩
  · exact h.elim0
  · exact ⟨Fin.castLE hd i, a (e j), hij⟩

/-- **Corollary 4.4** of [waldschmidt2000]: the case `d₀ = 1`, `d₁ = n = d` of
`schneiderLang`.

If `x 1, …, x d` are `ℚ`-linearly independent with algebraic coordinates, if
`y 1, …, y d` is a basis of `ℂᵈ` over `ℂ` whose first coordinates `y j 0` are all
algebraic, then one at least of the `d ^ 2` numbers `x i · y j` is not a logarithm of an
algebraic number.

For `d = 1` this is the theorem of Hermite–Lindemann. -/
theorem schneiderLang_one {d : ℕ} [NeZero d] (x : Fin d → Fin d → ℂ)
    (hx : ∀ i v, IsAlgebraic ℚ (x i v)) (hxli : LinearIndependent ℚ x)
    (y : Fin d → Fin d → ℂ) (hyli : LinearIndependent ℂ y)
    (hy₁ : ∀ j, IsAlgebraic ℚ (y j 0)) :
    ∃ i j : Fin d, ¬ IsAlgebraic ℚ (exp (∑ v, x i v * y j v)) := by
  have h1d : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  rcases schneiderLang h1d (by omega) x hx hxli y hyli with ⟨h, j, hj⟩ | ⟨i, j, hij⟩
  · -- the `d₀ = 1` coordinates are the `y j 0`, which are algebraic by hypothesis
    exact absurd (hy₁ j) (by rwa [Subsingleton.elim h 0, show Fin.castLE h1d 0 = 0 from rfl] at hj)
  · exact ⟨i, j, hij⟩

end Transcendental
