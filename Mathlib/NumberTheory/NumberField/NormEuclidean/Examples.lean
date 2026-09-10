/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.NormEuclidean.Density
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion

/-!
# A worked example of Heilbronn's criterion

The criterion of
`Mathlib.NumberTheory.NumberField.NormEuclidean.Density` takes a number field, an algebraic
integer generating it, and a list of arithmetic conditions on the coefficients of its minimal
polynomial.  This file carries all of that out for one concrete polynomial, `X ^ 3 + 5 X + 5`,
and so exhibits a specific field that is not norm-Euclidean.

The work is: Eisenstein at `5` gives irreducibility over `ℤ` and hence over `ℚ`
(`Polynomial.irreducible_of_eisenstein_criterion`), `AdjoinRoot` of the result is a cubic number
field, its generating root is an algebraic integer, and the two rootlessness conditions are finite
computations in `ZMod 2` and `ZMod 3`.

## Main results

* `NumberField.irreducible_X_pow_three_add_five_X_add_five` and
  `NumberField.irreducible_map_X_pow_three_add_five_X_add_five`:  irreducibility over `ℤ` and
  over `ℚ`, by Eisenstein at `5`.
* `NumberField.not_normEuclidean_adjoinRoot_X_pow_three_add_five_X_add_five`:  the field
  `ℚ[x] / (x ^ 3 + 5 x + 5)` is not norm-Euclidean.  The statement has no hypotheses.

## References

The example is of the shape considered in [Hibbler, McGown, Treviño, *Polynomial densities and
Heilbronn's criterion*][hibbler_mcgown_trevino2025]; the density theorems say that a positive
proportion of the polynomials of this degree behave in the same way.
-/

public section

open Polynomial NumberField

namespace NumberField

set_option linter.style.haveILetI false

/-- `X ^ 3 + 5 X + 5` is monic. -/
theorem monic_X_pow_three_add_five_X_add_five : (X ^ 3 + 5 * X + 5 : ℤ[X]).Monic := by
  have h : (X ^ 3 + 5 * X + 5 : ℤ[X]) = X ^ 3 + (5 * X + 5) := by ring
  rw [h]
  refine monic_X_pow_add ?_
  compute_degree!

/-- `X ^ 3 + 5 X + 5` is irreducible over `ℤ`, by Eisenstein's criterion at `5`. -/
theorem irreducible_X_pow_three_add_five_X_add_five :
    Irreducible (X ^ 3 + 5 * X + 5 : ℤ[X]) := by
  have hmon := monic_X_pow_three_add_five_X_add_five
  have hdeg : (X ^ 3 + 5 * X + 5 : ℤ[X]).degree = 3 := by compute_degree!
  refine irreducible_of_eisenstein_criterion (P := Ideal.span {(5 : ℤ)}) ?_ ?_ ?_ ?_ ?_
    hmon.isPrimitive
  · exact (Ideal.span_singleton_prime (by norm_num)).2
      (by rw [Int.prime_iff_natAbs_prime]; exact Nat.prime_five)
  · rw [hmon.leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [hdeg] at hk
    have hk3 : k < 3 := by exact_mod_cast hk
    rw [Ideal.mem_span_singleton]
    interval_cases k <;> simp [coeff_add, coeff_X_pow, coeff_ofNat_succ]
  · rw [hdeg]; norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp [coeff_add, coeff_X_pow]

/-- `X ^ 3 + 5 X + 5` is irreducible over `ℚ`:  it is primitive, being monic. -/
theorem irreducible_map_X_pow_three_add_five_X_add_five :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (X ^ 3 + 5 * X + 5 : ℤ[X])) :=
  (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    monic_X_pow_three_add_five_X_add_five.isPrimitive).1
      irreducible_X_pow_three_add_five_X_add_five

instance : Fact (Irreducible (Polynomial.map (Int.castRingHom ℚ) (X ^ 3 + 5 * X + 5 : ℤ[X]))) :=
  ⟨irreducible_map_X_pow_three_add_five_X_add_five⟩

/-- **A concrete field to which the criterion applies.**  The polynomial `X ^ 3 + 5 X + 5` is
Eisenstein at `5`, has no root modulo `2` and none modulo `3`, and `5 = 1 · 2 + 1 · 3` with
`2 ∤ 1` and `3 ∤ 1`; since `gcd (5 - 1, 3) = 1`, Heilbronn's criterion applies and the cubic field
it generates is not norm-Euclidean. -/
theorem not_normEuclidean_adjoinRoot_X_pow_three_add_five_X_add_five :
    ¬ ∀ α β : 𝓞 (AdjoinRoot (Polynomial.map (Int.castRingHom ℚ) (X ^ 3 + 5 * X + 5 : ℤ[X]))),
      β ≠ 0 → ∃ γ ρ : 𝓞 (AdjoinRoot (Polynomial.map (Int.castRingHom ℚ)
        (X ^ 3 + 5 * X + 5 : ℤ[X]))), α = γ * β + ρ ∧
        (Algebra.norm ℤ ρ).natAbs < (Algebra.norm ℤ β).natAbs := by
  set g : ℚ[X] := Polynomial.map (Int.castRingHom ℚ) (X ^ 3 + 5 * X + 5 : ℤ[X]) with hg
  have hmonZ := monic_X_pow_three_add_five_X_add_five
  have hgmon : g.Monic := by rw [hg]; exact hmonZ.map _
  have hgne : g ≠ 0 := hgmon.ne_zero
  have hgdeg : g.natDegree = 3 := by rw [hg, hmonZ.natDegree_map]; compute_degree!
  have : FiniteDimensional ℚ (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hgne).basis
  have : NumberField (AdjoinRoot g) := ⟨⟩
  have hdeg : Module.finrank ℚ (AdjoinRoot g) = 3 := by
    rw [(AdjoinRoot.powerBasis hgne).finrank]; exact hgdeg
  -- the defining equation of the root
  have key : Polynomial.eval₂ (algebraMap ℤ (AdjoinRoot g)) (AdjoinRoot.root g)
      (X ^ 3 + 5 * X + 5 : ℤ[X]) = 0 := by
    have h2 : (algebraMap ℤ (AdjoinRoot g)) = (AdjoinRoot.of g).comp (algebraMap ℤ ℚ) := by
      ext n; simp
    rw [h2, ← Polynomial.eval₂_map, algebraMap_int_eq, ← hg]
    exact AdjoinRoot.eval₂_root g
  have key' : (AdjoinRoot.root g) ^ 3 + 5 * (AdjoinRoot.root g) + 5 = 0 := by
    have h := key
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat] at h
    linear_combination h
  have hint : IsIntegral ℤ (AdjoinRoot.root g) := ⟨_, hmonZ, key⟩
  -- the root as an algebraic integer
  set θ : 𝓞 (AdjoinRoot g) := ⟨AdjoinRoot.root g, hint⟩ with hθ
  have hθcoe : (algebraMap (𝓞 (AdjoinRoot g)) (AdjoinRoot g)) θ = AdjoinRoot.root g := rfl
  have hroot : θ ^ 3 + ∑ i : Fin 3, ((![5, 5, 0] i : ℤ) : 𝓞 (AdjoinRoot g)) * θ ^ (i : ℕ) = 0 := by
    refine RingOfIntegers.coe_injective ?_
    push_cast [Fin.sum_univ_succ, Fin.sum_univ_zero, hθcoe]
    norm_num
    simp only [map_ofNat]
    linear_combination key'
  -- apply the criterion
  have heval : ∀ (R : Type) [CommRing R] (r : R),
      Polynomial.eval r (X ^ 3 + ∑ i : Fin 3, C (((![5, 5, 0] i : ℤ) : R)) * X ^ (i : ℕ))
        = r ^ 3 + 5 + 5 * r := by
    intro R _ r
    -- `simp` expands the three-term sum and pushes `eval` through; the `Fin.val` exponents it
    -- leaves are settled by `ring`
    simp [Fin.sum_univ_succ]
    ring
  refine not_normEuclidean_of_eisensteinDumas_fin (n := 3) (m := 1) (p := 5) (q₁ := 2) (q₂ := 3)
    (a := ![5, 5, 0]) (c := ![1, 1, 1]) (by omega) Nat.prime_five (by omega) (by decide)
    (by decide) hdeg hroot ?_ ?_ ?_ Nat.prime_two Nat.prime_three ?_ ?_ ?_
  · decide
  · decide
  · simp
  · exact ⟨1, 1, by omega, by omega, by omega, by decide, by decide⟩
  · have h2 : ∀ r : ZMod 2, ¬ (r ^ 3 + 5 + 5 * r = 0) := by decide
    intro r
    rw [Polynomial.IsRoot, heval]
    exact h2 r
  · have h3 : ∀ r : ZMod 3, ¬ (r ^ 3 + 5 + 5 * r = 0) := by decide
    intro r
    rw [Polynomial.IsRoot, heval]
    exact h3 r

end NumberField
