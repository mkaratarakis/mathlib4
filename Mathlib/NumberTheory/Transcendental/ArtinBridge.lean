/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.RingTheory.FreeCommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

/-!
# Algebra core of the Artin eval↔formula bridge

To encode `∃ x, f(x) < 0` (for `f : MvPolynomial σ ℝ`) as a first-order formula over the language of
ordered rings — with the real coefficients of `f` as parameters — one first represents `f` as an
element `Artin.ModelTheory.polyFree f` of the free commutative ring over `ℝ ⊕ σ`, using a generator
`inl r` for each real coefficient `r` and `inr i` for each indeterminate `i`.

`lift_polyFree` shows the key fact: lifting `polyFree f` along a coefficient ring hom `c` and a point
`x` recovers `MvPolynomial.eval₂ c x f`. Composing with `FirstOrder.Ring.termOfFreeCommRing`
(whose realization is exactly `FreeCommRing.lift`) turns `polyFree f` into an ordered-ring term whose
realization is the polynomial value — the algebra half of the bridge.
-/

open MvPolynomial

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

end Artin.ModelTheory
