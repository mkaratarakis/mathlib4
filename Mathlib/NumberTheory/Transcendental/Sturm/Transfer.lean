/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Theorem

/-!
# Transfer of Sturm data along a field embedding

Toward the quantifier-elimination core: the Sturm sign-variation count is invariant under an
order-preserving embedding of real closed fields, so the number of real roots of a polynomial with
coefficients in `K` is the same whether counted in `K` or a real closed extension `L`. This is the
semantic heart of quantifier elimination — realizable sign conditions are determined by the
coefficients, hence transfer between a real closed field and any real closed extension.

The first brick: the Sturm sequence commutes with `Polynomial.map φ` for a ring embedding `φ` of
fields (`sturmSeq_map`), because polynomial remainder commutes with `map` over a field
(`Polynomial.map_mod`).
-/

open Polynomial

namespace Sturm

variable {K L : Type*} [Field K] [LinearOrder K] [Field L] [LinearOrder L]

/-- One-step unfolding of the Sturm sequence at `0`. -/
theorem sturmSeq_zero (g : K[X]) : sturmSeq 0 g = [] := by
  unfold sturmSeq; simp

/-- One-step unfolding of the Sturm sequence at a nonzero head. -/
theorem sturmSeq_cons {f g : K[X]} (hf : f ≠ 0) :
    sturmSeq f g = f :: sturmSeq g (-f % g) := by
  conv_lhs => unfold sturmSeq
  rw [if_neg hf]

/-- The Sturm sequence commutes with `Polynomial.map` along a field hom: mapping the whole sequence
equals the Sturm sequence of the mapped polynomials. -/
theorem sturmSeq_map (φ : K →+* L) (f g : K[X]) :
    (sturmSeq f g).map (Polynomial.map φ) = sturmSeq (f.map φ) (g.map φ) := by
  induction f, g using sturmSeq.induct with
  | case1 g =>
    rw [sturmSeq_zero, Polynomial.map_zero, sturmSeq_zero, List.map_nil]
  | case2 f g hf ih =>
    have hfφ : f.map φ ≠ 0 := by rwa [Ne, Polynomial.map_eq_zero_iff φ.injective]
    rw [sturmSeq_cons hf, List.map_cons, sturmSeq_cons hfφ, ih, Polynomial.map_mod,
      Polynomial.map_neg]

end Sturm
