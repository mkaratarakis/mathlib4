/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
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
  `d₀ ≤ n < d₀ + d₁`, `ℚ`-linearly independent `x 1, …, x d₁` in `ℂⁿ` with algebraic coordinates, and a basis
  `y 1, …, y n` of `ℂⁿ` over `ℂ`, one of the `(d₀ + d₁) * n` numbers `y j h`
  (`h < d₀`) and `exp (x i · y j)` is transcendental.
* `Transcendental.schneiderLang_zero`: **Corollary 4.3**, the case `d₀ = 0`, phrased as
  in the book with a family of rank at least `n + 1` and a spanning family of `ℂⁿ`.
* `Transcendental.schneiderLang_one`: **Corollary 4.4**, the case `d₀ = 1`, `d₁ = n = d`.

`schneiderLang_zero` yields the homogeneous case of Baker's theorem and
`schneiderLang_one` the nonhomogeneous case; both deductions are in
`Mathlib/NumberTheory/Transcendental/Baker/Reduction.lean`.

## What remains

`schneiderLang` is the one open statement in this directory; everything else, including
Baker's theorem itself, is proved from it.  Its proof is §§4.3-4.6 of [waldschmidt2000], in
dependency order:

* **§4.3, Lemma 4.8** — division in the ring of entire functions by a monic polynomial in one
  coordinate, with sup-norm estimates, by a double induction on the degree and on the number
  of variables.  The analytic content is available: `MultiIndex.hasSum_split_coord` is the
  degree-one case, `MultiIndex.hasSum_smul_shift` divides by a coordinate, and
  `MultiIndex.hasSum_coeff` with `analyticAt_tsum_monomial` moves between a function and its
  multi-index series.  What is left is the estimates (`Aₚ ≤ 3ᵖ` of step 2.4, the constants of
  step 3.6) and the bookkeeping of the induction.
* **§4.3, Proposition 4.7** — the Schwarz lemma for Cartesian products, from Lemma 4.8.  The
  maximum modulus principle is available in the needed generality:
  `Complex.norm_le_of_forall_mem_frontier_norm_le` is stated for an arbitrary complex normed
  domain, and the closed polydisc is `Metric.closedBall` for the `Pi` sup norm.
* **§4.4, Lemma 4.9** — the value of `D^σ (z^τ e^{t·z})` at a lattice point, with bounds on the
  degree and length of the resulting polynomial.  Combinatorial; needs a multi-index
  derivative API on a product domain, which mathlib does not have.
* **§4.5, Proposition 4.10** — an auxiliary function small on a disc, from Lemmas 4.12 and
  4.13.  `ThueSiegel.exists_int_vec_abs_le_of_pow_lt` (Lemma 4.11) is proved.
* **§4.6** — the transcendence argument, with the parameter choices and the constants
  `c₁, …, c₁₃`.  It also needs a Liouville inequality: a lower bound for a nonzero algebraic
  number in terms of its degree and house.  Mathlib has `NumberField.house` and the `Height`
  directory but not that inequality.

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
      ∃ (i : Fin d₁) (j : Fin n), Transcendental ℚ (exp (∑ v, x i v * y j v)) := by
  sorry

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
  haveI : Fintype κ := IsNoetherian.fintypeBasisIndex B
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
