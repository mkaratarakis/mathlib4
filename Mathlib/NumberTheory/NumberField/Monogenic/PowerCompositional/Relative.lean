/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Main
public import Mathlib.NumberTheory.NumberField.Monogenic.Relative

/-!
# Power compositional polynomials over a number field base

Problem 2 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*, Finite Fields Appl. **107** (2025), 102642,
asks for necessary and sufficient conditions for `f(X ^ k)` to be monogenic over an arbitrary
number field base, rather than over `ℚ`.  This file proves the *necessity* half of the
relative analogue of their Theorem 1.1.

The organising notion is `NumberField.Relative.IsIndexDivisor π f`: a decomposition
`f = h ^ 2 g + π (k h) + π ^ 2 t` with `h * g` monic of degree `< deg f`.  Over `ℤ` this is,
by Uchida's criterion, equivalent to `p` dividing the index; over a general base only one
implication is available (`NumberField.Relative.adjoin_ne_top_of_isIndexDivisor`), and that
is the direction the results below use.

## Main results

* `NumberField.Relative.IsIndexDivisor.expand`: **Lemma 2.6, relative version** --- an index
  divisor of `f` is an index divisor of `f(X ^ ℓ)`.  Unlike the absolute proof, which goes
  through Uchida's criterion, this one is immediate: applying `X ↦ X ^ ℓ` to a decomposition
  gives a decomposition, and `expand` multiplies all degrees by `ℓ`.

* `NumberField.Relative.isIndexDivisor_expand_of_sq_dvd_coeff_zero`: **Proposition 2.3,
  relative version** --- if `π ^ 2` divides `f(0)` and `ℓ ≥ 2` then `π` is an index divisor
  of `f(X ^ ℓ)`.

* `NumberField.Relative.adjoin_ne_top_of_sq_dvd_coeff_zero`: consequently, if `f(X ^ ℓ)` is
  monogenic over `𝓞 K` with `ℓ ≥ 2`, then no square of a prime of `𝓞 K` divides `f(0)`.
  This is condition (3) of Theorem 1.1, and it is necessary over any number field base.

* `NumberField.Relative.adjoin_ne_top_of_isIndexDivisor_expand`: likewise condition (1) is
  necessary: an index divisor of `f` obstructs monogenity of `f(X ^ k)`.

## What is missing for Problem 2

The converse direction needs the existence half of Uchida's criterion over `𝓞 K` --- that
`π` dividing the index *produces* a decomposition --- which is
`RingOfIntegers.exists_splitting_of_dvd_exponent` in the absolute case and is not yet
available relatively.  Two further points where the relative case genuinely differs from the
absolute one, and which any solution of Problem 2 must address:

* the residue field `𝓞 K ⧸ (π)` need not be prime, so the identity `f(X ^ p) ≡ f ^ p` modulo
  `π` used throughout Section 2 becomes a Frobenius *twist* `f(X ^ p) ≡ (f ^ σ) ^ p`, where
  `σ` is the inverse of the Frobenius of the residue field;
* the base need not be principal, so a prime *element* `π` need not exist at all; the global
  packaging `NumberField.Relative.adjoin_eq_top_of_forall_prime_saturated` currently assumes
  `IsPrincipalIdealRing (𝓞 K)`.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace NumberField.Relative

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
  [Algebra K K₁] {θ : 𝓞 K₁}

/-- `π` **is an index divisor of** `f`: a decomposition `f = h ^ 2 g + π (k h) + π ^ 2 t`
with `h * g` monic of degree below that of `f`.

Over `ℤ` this is equivalent, by Uchida's criterion, to `p` dividing the index
`[𝓞 K : ℤ[θ]]` --- compare `Polynomial.IsIndexDivisor`.  Over a general base the
implication `IsIndexDivisor → not monogenic` is
`NumberField.Relative.adjoin_ne_top_of_isIndexDivisor`; the converse is open. -/
def IsIndexDivisor {K : Type*} [Field K] [NumberField K] (π : 𝓞 K) (f : (𝓞 K)[X]) : Prop :=
  ∃ h g k t : (𝓞 K)[X], (h * g).Monic ∧ (h * g).natDegree < f.natDegree ∧
    f = h ^ 2 * g + C π * (k * h) + C π ^ 2 * t

/-- An index divisor of the minimal polynomial obstructs monogenity. -/
theorem adjoin_ne_top_of_isIndexDivisor {π : 𝓞 K} (hπ : Prime π)
    (h : IsIndexDivisor π (minpoly (𝓞 K) θ)) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ := by
  obtain ⟨a, b, c, d, hm, hdeg, heq⟩ := h
  exact adjoin_ne_top_of_sq_factor hπ hm hdeg heq

/-- **Lemma 2.6, relative version.**  An index divisor of `f` is an index divisor of
`f(X ^ ℓ)`.

Substituting `X ^ ℓ` in a decomposition `f = h ^ 2 g + π (k h) + π ^ 2 t` gives one for
`f(X ^ ℓ)`, since `expand` is a ring homomorphism fixing the constants; it multiplies all
degrees by `ℓ`, so the degree condition is preserved.  No form of Uchida's criterion is
needed. -/
theorem IsIndexDivisor.expand {π : 𝓞 K} {f : (𝓞 K)[X]} {ℓ : ℕ} (hℓ : 0 < ℓ)
    (h : IsIndexDivisor π f) : IsIndexDivisor π (Polynomial.expand (𝓞 K) ℓ f) := by
  obtain ⟨a, b, c, d, hm, hdeg, heq⟩ := h
  refine ⟨Polynomial.expand (𝓞 K) ℓ a, Polynomial.expand (𝓞 K) ℓ b,
    Polynomial.expand (𝓞 K) ℓ c, Polynomial.expand (𝓞 K) ℓ d, ?_, ?_, ?_⟩
  · rw [← map_mul]
    exact hm.expand hℓ
  · rw [← map_mul, natDegree_expand, natDegree_expand]
    exact (Nat.mul_lt_mul_right hℓ).mpr hdeg
  · rw [heq]
    simp only [map_add, map_mul, map_pow, expand_C]

/-- **Proposition 2.3, relative version.**  If `π ^ 2` divides `f(0)` and `ℓ ≥ 2`, then `π`
is an index divisor of `f(X ^ ℓ)`.

The witness is the same as in the absolute case: `f(X ^ ℓ)` has no terms in degrees `1` to
`ℓ - 1`, so `f(X ^ ℓ) - f(0)` is divisible by `X ^ 2`, and `f(0)` is divisible by `π ^ 2`. -/
theorem isIndexDivisor_expand_of_sq_dvd_coeff_zero {π : 𝓞 K} (hπ : Prime π) {f : (𝓞 K)[X]}
    (hf : f.Monic) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hπ2 : π ^ 2 ∣ f.coeff 0) :
    IsIndexDivisor π (Polynomial.expand (𝓞 K) ℓ f) := by
  have hℓ0 : 0 < ℓ := by omega
  set F := Polynomial.expand (𝓞 K) ℓ f with hFdef
  have hFm : F.Monic := hf.expand hℓ0
  -- `f` is nonconstant: otherwise `f = 1` and `π ^ 2 ∣ 1`.
  have hfd : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h
    · exfalso
      rw [hf.natDegree_eq_zero.mp h0] at hπ2
      simp only [coeff_one_zero] at hπ2
      exact hπ.not_unit (isUnit_of_dvd_one ((dvd_pow_self π two_ne_zero).trans hπ2))
    · exact h
  have hFd : 0 < F.natDegree := by
    rw [hFdef, natDegree_expand]
    positivity
  have hF0 : F.coeff 0 = f.coeff 0 := by
    rw [hFdef, coeff_expand hℓ0]
    simp
  -- `X ^ 2` divides `F - F(0)`.
  obtain ⟨G, hG⟩ : (X : (𝓞 K)[X]) ^ 2 ∣ F - C (F.coeff 0) := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp
    · rw [coeff_sub, coeff_C, hFdef, coeff_expand hℓ0]
      simp [Nat.dvd_one.not.mpr (by omega : ℓ ≠ 1)]
  have hdegC : (C (F.coeff 0)).degree < F.degree :=
    lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.mp hFd)
  have hXG2 : ((X : (𝓞 K)[X]) ^ 2 * G).Monic := hG ▸ hFm.sub_of_left hdegC
  have hXG : ((X : (𝓞 K)[X]) * G).Monic := by
    refine monic_X.of_mul_monic_left ?_
    rw [show (X : (𝓞 K)[X]) * ((X : (𝓞 K)[X]) * G) = X ^ 2 * G by ring]
    exact hXG2
  have hG0 : G ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXG2
    exact not_monic_zero hXG2
  have hnd : ((X : (𝓞 K)[X]) * G).natDegree < F.natDegree := by
    have h2 : ((X : (𝓞 K)[X]) ^ 2 * G).natDegree = F.natDegree := by
      rw [← hG, natDegree_sub_C]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hG0, natDegree_X_pow] at h2
    rw [natDegree_mul X_ne_zero hG0, natDegree_X]
    omega
  obtain ⟨c, hc⟩ := hπ2
  refine ⟨X, G, 0, C c, hXG, hnd, ?_⟩
  have hCF0 : C (F.coeff 0) = C π ^ 2 * C c := by
    rw [hF0, hc, map_mul, map_pow]
  rw [← hCF0]
  linear_combination hG

/-! ### Necessity of the conditions of Theorem 1.1 over a number field base -/

/-- **Condition (3) of Theorem 1.1 is necessary over any number field base.**  If `θ` is a
root of `f(X ^ ℓ)` with `ℓ ≥ 2` and `𝓞 K[θ]` is the full ring of integers, then no square of
a prime of `𝓞 K` divides `f(0)`. -/
theorem adjoin_ne_top_of_sq_dvd_coeff_zero {π : 𝓞 K} (hπ : Prime π) {f : (𝓞 K)[X]}
    (hf : f.Monic) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hπ2 : π ^ 2 ∣ f.coeff 0)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) ℓ f) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ :=
  adjoin_ne_top_of_isIndexDivisor hπ
    (hmin ▸ isIndexDivisor_expand_of_sq_dvd_coeff_zero hπ hf hℓ hπ2)

/-- **Condition (1) of Theorem 1.1 is necessary over any number field base.**  If `π` is an
index divisor of `f` and `θ` is a root of `f(X ^ ℓ)`, then `𝓞 K[θ]` is not the full ring of
integers. -/
theorem adjoin_ne_top_of_isIndexDivisor_expand {π : 𝓞 K} (hπ : Prime π) {f : (𝓞 K)[X]}
    {ℓ : ℕ} (hℓ : 0 < ℓ) (h : IsIndexDivisor π f)
    (hmin : minpoly (𝓞 K) θ = Polynomial.expand (𝓞 K) ℓ f) :
    Algebra.adjoin (𝓞 K) {θ} ≠ ⊤ :=
  adjoin_ne_top_of_isIndexDivisor hπ (hmin ▸ h.expand hℓ)

end NumberField.Relative
