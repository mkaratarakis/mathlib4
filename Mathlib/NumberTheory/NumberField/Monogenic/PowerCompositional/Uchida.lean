/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Dedekind
public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Ideal

/-!
# Uchida's criterion, in terms of ideals of `ℤ[X]`

K. Uchida, *When is `ℤ[θ]` the ring of integers?* (Osaka J. Math. **14** (1977), 155–157)
characterises the primes dividing the index `[𝓞 K : ℤ[θ]]` as those `p` for which the
minimal polynomial `f` of `θ` lies in `𝔪 ^ 2` for some maximal ideal `𝔪 = ⟨p, g⟩` of
`ℤ[X]`, with `g` monic and irreducible mod `p`.  This is the form in which the whole of
Section 2 of Kaur–Kumar–Remete is stated.

This file provides the nontrivial half: `p ∣ exponent θ` implies such an `𝔪` exists.  It
is a repackaging of `RingOfIntegers.exists_splitting_of_dvd_exponent`, which supplies a
splitting `f = A * B + p * N` with a common irreducible factor `π` of the reductions of
`A`, `B` and `N`; membership of `f` in `⟨p, π⟩ ^ 2` is then immediate, since each of `A`,
`B`, `N` lies in `⟨p, π⟩` by `Polynomial.mem_span_pair_C_natCast_iff`.

## Main results

* `RingOfIntegers.exists_monic_irreducible_minpoly_mem_sq_of_dvd_exponent`: Uchida's
  criterion, existence half.

## Implementation notes

The converse — that `f ∈ ⟨p, g⟩ ^ 2` forces `p ∣ exponent θ` — is available as
`RingOfIntegers.dvd_exponent_of_sq_factor`, but in a form carrying two extra hypotheses on
the cofactor (monicity and a degree bound).  Supplying those from bare ideal membership
requires normalising the decomposition, and is not done here; consequently this file states
only the one implication rather than a biconditional.

## References

* [K. Uchida, *When is `ℤ[θ]` the ring of integers?*][Uchida1977]
* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
variable {p : ℕ} [hp : Fact p.Prime]

/-- **Uchida's criterion, existence half.**  If the rational prime `p` divides the index
`[𝓞 K : ℤ[θ]]`, then the minimal polynomial of `θ` lies in the square of a maximal ideal
`⟨p, Pi⟩` of `ℤ[X]` with `Pi` monic and irreducible mod `p`. -/
theorem exists_monic_irreducible_minpoly_mem_sq_of_dvd_exponent
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hdvd : p ∣ exponent θ) :
    ∃ Pi : ℤ[X], Pi.Monic ∧ Irreducible (Pi.map (Int.castRingHom (ZMod p))) ∧
      minpoly ℤ θ ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) ^ 2 := by
  obtain ⟨π, A, B, N, hπmonic, hπirr, hsplit, hπA, hπB, hπN⟩ :=
    exists_splitting_of_dvd_exponent hθ hdvd
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  -- Lift `π` to a monic polynomial over `ℤ`.
  obtain ⟨Pi, hPimap, -, hPimonic⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts π).mpr
      (Polynomial.map_surjective _ hsurj π)) hπmonic
  refine ⟨Pi, hPimonic, by rw [hPimap]; exact hπirr, ?_⟩
  -- Each of `A`, `B`, `N` lies in `⟨p, Pi⟩`, as does `p` itself.
  have hmemA : A ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) :=
    mem_span_pair_C_natCast_iff.mpr (by rw [hPimap]; exact hπA)
  have hmemB : B ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) :=
    mem_span_pair_C_natCast_iff.mpr (by rw [hPimap]; exact hπB)
  have hmemN : N ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) :=
    mem_span_pair_C_natCast_iff.mpr (by rw [hPimap]; exact hπN)
  have hmemp : (C (p : ℤ) : ℤ[X]) ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) :=
    Ideal.subset_span (by simp)
  -- `f = A * B + p * N` with all four factors in `⟨p, Pi⟩`.
  rw [hsplit, sq]
  exact Ideal.add_mem _ (Ideal.mul_mem_mul hmemA hmemB) (Ideal.mul_mem_mul hmemp hmemN)

end RingOfIntegers
