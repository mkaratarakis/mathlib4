/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Sturm.Theorem

/-!
# Root existence over a real closed field is decided by Sturm's theorem

A corollary of the ported Sturm–Tarski machinery: over a real closed field, a nonzero polynomial
has a root iff the Sturm sign-variation count `seqVarRSturm p p'` is positive. This is the
single-equation core of the sign-condition realizability that drives quantifier elimination
(`RCF_ex_isQFEquivalent`): solvability of `p(x) = 0` is a decidable condition on the coefficients,
computed by the (algebraic) Sturm sequence.
-/

noncomputable section

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Root existence via Sturm.** A nonzero polynomial over a real closed field has a root iff its
total Sturm sign-variation count is positive. -/
theorem exists_isRoot_iff_seqVarRSturm_pos {p : R[X]} (hp : p ≠ 0) :
    (∃ x, p.IsRoot x) ↔ 0 < seqVarRSturm p (derivative p) := by
  rw [← sturm_R, Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp, hx⟩)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_roots'.mp (Multiset.mem_toFinset.mp hx)).2⟩

end
