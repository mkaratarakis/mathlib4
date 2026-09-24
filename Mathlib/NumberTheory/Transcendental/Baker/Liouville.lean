/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.NumberField.Norm

/-!
# Liouville's inequality

A nonzero algebraic integer cannot be small at any embedding: its size there is bounded below
in terms of its house and the degree of the field.  This is the arithmetic lower bound that a
transcendence proof plays against an analytic upper bound.

`Mathlib/NumberTheory/NumberField/House.lean` already provides
`NumberField.norm_norm_le_norm_mul_house_pow`, bounding the field norm by one embedding times
a power of the house; all that is added here is that the norm of a nonzero algebraic integer
is at least one.

## Main statements

* `NumberField.one_le_norm_embedding_mul_house_pow`

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic
  Groups*][waldschmidt2000], Lemma 3.14
-/

@[expose] public section

open Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality.**  A nonzero algebraic integer cannot be small at any embedding:
its size there is at least `house α ^ -(d - 1)`, where `d = [K : ℚ]`.

This is the arithmetic half of a transcendence proof: the lower bound that an analytic upper
bound is played against. -/
theorem one_le_norm_embedding_mul_house_pow {α : 𝓞 K} (hα : α ≠ 0) (σ : K →+* ℂ) :
    1 ≤ ‖σ (α : K)‖ * house (α : K) ^ (Module.finrank ℚ K - 1) := by
  have hint : Algebra.norm ℤ α ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]
    exact hα
  have h1 : (1 : ℝ) ≤ ‖Algebra.norm ℚ (α : K)‖ := by
    have h2 : (1 : ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs hint
    have h4 : (1 : ℝ) ≤ |((Algebra.norm ℤ α : ℤ) : ℝ)| := by exact_mod_cast h2
    rw [← Algebra.coe_norm_int]
    simpa [Int.norm_eq_abs] using h4
  exact h1.trans (norm_norm_le_norm_mul_house_pow (α : K) σ)

end NumberField
