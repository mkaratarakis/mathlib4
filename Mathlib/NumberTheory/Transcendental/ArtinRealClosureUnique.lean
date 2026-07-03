/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.Transcendental.Hilbert17FTA

/-!
# Toward uniqueness of real closures: rigidity of real closed fields

The uniqueness of the real closure of an ordered field `F` splits into two halves:

* **existence of an `F`-algebra homomorphism** between two real closures — the hard half, needing
  root-counting transfer (`Sturm.card_roots_map_congr`) and root-matching; and
* **rigidity** — any such homomorphism is automatically an order-preserving *isomorphism*.

This file proves the rigidity half, sorry-free:

* `natDegree_le_two_of_irreducible` — over a real closed field, irreducible polynomials have
  degree at most `2` (via the algebraically closed quadratic extension `R[i]`,
  `isAlgClosed_adjoinRoot`);
* `algebraMap_surjective_of_isAlgebraic` — **a real closed field has no proper ordered algebraic
  extension**: if `L` is an ordered field, algebraic over a real closed subfield `R`, then
  `R = L`. A minimal polynomial of degree `2` either has square discriminant — and then the
  quadratic formula puts the root in `R` — or negative discriminant, and then the completed
  square `(2y + b)² = b² - 4c < 0` is a contradiction in the ordered field `L`;
* `algHom_bijective_of_isAlgebraic` / `algEquivOfRealClosures` — an `F`-algebra homomorphism
  between real closures of `F` is a bijection, upgraded to an `F`-algebra isomorphism.

Together with `Sturm.strictMono_map` (ring homomorphisms of real closed fields are automatically
order-preserving, since nonnegatives are squares), this reduces the uniqueness of real closures to
the existence of an `F`-algebra homomorphism.
-/

open Polynomial

namespace Hilbert17Blueprint

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Irreducible polynomials over a real closed field have degree at most two.** The quadratic
extension `R[i]` is algebraically closed (`isAlgClosed_adjoinRoot`), so any irreducible `p` has a
root `z` there; the degree of `p` is then `[R(z) : R]`, which divides `[R[i] : R] = 2`. -/
theorem natDegree_le_two_of_irreducible {p : R[X]} (hp : Irreducible p) : p.natDegree ≤ 2 := by
  haveI : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩
  haveI := isAlgClosed_adjoinRoot (R := R)
  set C := AdjoinRoot (X ^ 2 + 1 : R[X]) with hC
  -- `C` is two-dimensional over `R`
  have hX2 : (X ^ 2 + 1 : R[X]) ≠ 0 := (Fact.out (p := Irreducible _)).ne_zero
  have hdim : Module.finrank R C = 2 := by
    rw [(AdjoinRoot.powerBasis hX2).finrank, AdjoinRoot.powerBasis_dim,
      ← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]
  haveI : FiniteDimensional R C := (AdjoinRoot.powerBasis hX2).finite
  -- `p` has a root `z` in the algebraically closed `C`
  have hdeg : p.degree ≠ 0 := by
    rw [degree_eq_natDegree hp.ne_zero]
    exact_mod_cast hp.natDegree_pos.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero C p hdeg
  have hzint : IsIntegral R z := .of_finite R z
  -- the degree of `p` is the degree of `minpoly R z`, which divides `2`
  have hmin : minpoly R z = p * Polynomial.C p.leadingCoeff⁻¹ :=
    (minpoly.eq_of_irreducible hp hz).symm
  have hnd : (minpoly R z).natDegree = p.natDegree := by
    rw [hmin, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
  have hdvd : Module.finrank R (IntermediateField.adjoin R {z}) ∣ Module.finrank R C :=
    ⟨Module.finrank (IntermediateField.adjoin R {z}) C,
      (Module.finrank_mul_finrank R (IntermediateField.adjoin R {z}) C).symm⟩
  rw [hdim, IntermediateField.adjoin.finrank hzint] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- **A real closed field has no proper ordered algebraic extension.** If `L` is an ordered field
and an algebraic extension of a real closed field `R`, then `algebraMap R L` is surjective: a
minimal polynomial of degree two has either a square discriminant (quadratic formula → the element
is already in `R`) or a negative one (the completed square would be negative in `L`). -/
theorem algebraMap_surjective_of_isAlgebraic [Algebra R L] [Algebra.IsAlgebraic R L] :
    Function.Surjective (algebraMap R L) := by
  intro y
  have hyint : IsIntegral R y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hirr : Irreducible (minpoly R y) := minpoly.irreducible hyint
  have hmonic : (minpoly R y).Monic := minpoly.monic hyint
  have h12 : (minpoly R y).natDegree = 1 ∨ (minpoly R y).natDegree = 2 := by
    have h2 := natDegree_le_two_of_irreducible hirr
    have h1 := hirr.natDegree_pos
    omega
  rcases h12 with h1 | h2
  · -- linear minimal polynomial: `y` is the image of the negated constant coefficient
    have hy : y + algebraMap R L ((minpoly R y).coeff 0) = 0 := by
      have h0 := minpoly.aeval R y
      rw [hmonic.eq_X_add_C h1] at h0
      simpa using h0
    exact ⟨-((minpoly R y).coeff 0), by rw [map_neg]; linarith⟩
  · -- quadratic minimal polynomial: complete the square
    -- the algebraic relation `y² + b y + c = 0`
    have hrel : algebraMap R L ((minpoly R y).coeff 0)
        + algebraMap R L ((minpoly R y).coeff 1) * y + y ^ 2 = 0 := by
      have h0 := minpoly.aeval R y
      rw [aeval_eq_sum_range, h2, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one] at h0
      have hlead : (minpoly R y).coeff 2 = 1 := by
        have hcn := hmonic.coeff_natDegree
        rwa [h2] at hcn
      rw [hlead] at h0
      simp only [Algebra.smul_def, map_one, pow_zero, pow_one, mul_one, one_mul] at h0
      linear_combination h0
    -- the completed square
    have key : (2 * y + algebraMap R L ((minpoly R y).coeff 1)) ^ 2
        = algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0) := by
      have hmap : algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0)
          = algebraMap R L ((minpoly R y).coeff 1) ^ 2
            - 4 * algebraMap R L ((minpoly R y).coeff 0) := by
        rw [map_sub, map_pow, map_mul, map_ofNat]
      rw [hmap]
      linear_combination 4 * hrel
    by_cases hsq : IsSquare ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0)
    · -- square discriminant: quadratic formula, the root is in `R`
      obtain ⟨e, he⟩ := hsq
      have he' : algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0)
          = algebraMap R L e * algebraMap R L e := by rw [he, map_mul]
      have hzero : (2 * y + algebraMap R L ((minpoly R y).coeff 1) - algebraMap R L e)
          * (2 * y + algebraMap R L ((minpoly R y).coeff 1) + algebraMap R L e) = 0 := by
        linear_combination key + he'
      have h2L : (2 : L) ≠ 0 := two_ne_zero
      rcases mul_eq_zero.mp hzero with h | h
      · refine ⟨(e - (minpoly R y).coeff 1) / 2, ?_⟩
        rw [map_div₀, map_sub, map_ofNat]
        field_simp
        linarith
      · refine ⟨(-e - (minpoly R y).coeff 1) / 2, ?_⟩
        rw [map_div₀, map_sub, map_neg, map_ofNat]
        field_simp
        linarith
    · -- negative discriminant: the completed square would be negative in `L`
      exfalso
      have hneg : (minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0 < 0 := by
        by_contra hge
        exact hsq (IsSquare.of_nonneg (le_of_not_gt hge))
      obtain ⟨e, he⟩ := IsSquare.of_nonneg
        (show (0 : R) ≤ -((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0) by linarith)
      have himg : algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0) < 0 := by
        have hmm : -algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0)
            = algebraMap R L e * algebraMap R L e := by rw [← map_mul, ← he, map_neg]
        have hne : algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0) ≠ 0 :=
          fun h => hneg.ne ((algebraMap R L).injective (h.trans (map_zero _).symm))
        have hle : algebraMap R L ((minpoly R y).coeff 1 ^ 2 - 4 * (minpoly R y).coeff 0) ≤ 0 :=
          neg_nonneg.mp (hmm ▸ mul_self_nonneg _)
        exact lt_of_le_of_ne hle hne
      exact absurd (key ▸ sq_nonneg (2 * y + algebraMap R L ((minpoly R y).coeff 1)))
        (not_le.mpr himg)

variable {F R₂ : Type*} [Field F] [Field R₂] [LinearOrder R₂] [IsStrictOrderedRing R₂]
  [IsRealClosed R₂] [Algebra F R] [Algebra F R₂]

omit [IsRealClosed R₂] in
/-- **Rigidity of real closures**: an `F`-algebra homomorphism from a real closed field into an
*ordered* algebraic extension of `F` is automatically bijective (the target need not be assumed
real closed). Injectivity is free (field homomorphism); surjectivity is
`algebraMap_surjective_of_isAlgebraic` applied over the image. -/
theorem algHom_bijective_of_isAlgebraic [Algebra.IsAlgebraic F R₂] (φ : R →ₐ[F] R₂) :
    Function.Bijective φ := by
  refine ⟨φ.toRingHom.injective, ?_⟩
  letI : Algebra R R₂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F R R₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Algebra.IsAlgebraic R R₂ := Algebra.IsAlgebraic.tower_top (K := F) R
  exact algebraMap_surjective_of_isAlgebraic (R := R) (L := R₂)

omit [IsRealClosed R₂] in
/-- **Uniqueness of real closures, modulo existence**: any `F`-algebra homomorphism between two
real closed algebraic extensions of `F` upgrades to an `F`-algebra isomorphism. Combined with
`Sturm.strictMono_map` (such maps are automatically order-preserving), the uniqueness of the real
closure is reduced to *existence* of an `F`-algebra homomorphism. -/
noncomputable def algEquivOfRealClosures [Algebra.IsAlgebraic F R₂] (φ : R →ₐ[F] R₂) :
    R ≃ₐ[F] R₂ :=
  AlgEquiv.ofBijective φ (algHom_bijective_of_isAlgebraic φ)

end Hilbert17Blueprint
