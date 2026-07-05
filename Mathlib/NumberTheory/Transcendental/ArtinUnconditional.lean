/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Artin
import Mathlib.NumberTheory.Transcendental.ArtinQE

/-!
# Artin's theorem, unconditionally

`Artin.artin` (Artin's solution of Hilbert's 17th problem) was proved modulo quantifier
elimination for the first-order theory of real closed fields. That hypothesis is now a theorem
(`Theory.RCF_hasQuantifierElimination`, via the compactness criterion
`isQFEquivalent_of_qf_transfer` and the quantifier-free-type transfer `realize_ex_transfer`,
powered by Sturm-theoretic root counting and the uniqueness of real closures). This file states
the unconditional result.
-/

open MvPolynomial

namespace Artin

/-- **Artin's theorem — Hilbert's 17th problem** (unconditional). A polynomial over `ℝ` that is
nonnegative at every real point is a sum of squares of rational functions. -/
theorem artin' {σ : Type*} [Finite σ] (f : MvPolynomial σ ℝ)
    (hf : ∀ a : σ → ℝ, 0 ≤ eval a f) :
    IsSumSq (algebraMap (MvPolynomial σ ℝ) (RatField σ) f) :=
  artin Artin.ModelTheory.Theory.RCF_hasQuantifierElimination f hf

end Artin
