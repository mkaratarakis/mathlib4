/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.Dedekind
public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Ideal
public import Mathlib.NumberTheory.NumberField.Monogenic.Pure

/-!
# Uchida's criterion, in terms of ideals of `ℤ[X]`

K. Uchida, *When is `ℤ[θ]` the ring of integers?* (Osaka J. Math. **14** (1977), 155–157)
characterises the primes dividing the index `[𝓞 K : ℤ[θ]]` as those `p` for which the
minimal polynomial `f` of `θ` lies in `𝔪 ^ 2` for some maximal ideal `𝔪 = ⟨p, g⟩` of
`ℤ[X]`, with `g` monic and irreducible mod `p`.  This is the form in which the whole of
Section 2 of Kaur–Kumar–Remete is stated.

The existence half repackages `RingOfIntegers.exists_splitting_of_dvd_exponent`, which
supplies a splitting `f = A * B + p * N` with a common irreducible factor `π` of the
reductions of `A`, `B` and `N`; membership of `f` in `⟨p, π⟩ ^ 2` is then immediate, since
each of `A`, `B`, `N` lies in `⟨p, π⟩` by `Polynomial.mem_span_pair_C_natCast_iff`.

## Main results

* `RingOfIntegers.exists_monic_irreducible_minpoly_mem_sq_of_dvd_exponent`: existence half.
* `RingOfIntegers.dvd_exponent_of_minpoly_mem_sq`: sufficiency half.
* `RingOfIntegers.dvd_exponent_iff_exists_monic_irreducible_minpoly_mem_sq`: the criterion.

## Implementation notes

The sufficiency half is `RingOfIntegers.dvd_exponent_of_sq_factor` with its two side
hypotheses discharged.  That lemma needs a monic cofactor of degree below `deg f`, which
bare ideal membership does not supply, so the decomposition is normalised first: divide `f`
by the monic polynomial `Pi ^ 2`; the remainder then has degree below `2 * deg Pi`, hence
reduces to `0` mod `p` by `Polynomial.C_dvd_of_mem_sq_of_natDegree_lt`, and dividing it by
`p` lands in `⟨p, Pi⟩` by `Polynomial.mem_span_pair_of_C_mul_mem_sq`.  The quotient is monic
because `Pi ^ 2 * q = f - r` is.

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

/-- **Uchida's criterion, sufficiency half.**  If the minimal polynomial of `θ` lies in
`⟨p, Pi⟩ ^ 2` for some monic nonconstant `Pi : ℤ[X]`, then `p` divides the index.

This is `RingOfIntegers.dvd_exponent_of_sq_factor` with its two side hypotheses discharged.
Bare ideal membership does not supply a monic cofactor of controlled degree, so the
decomposition is normalised first: divide `f` by the monic polynomial `Pi ^ 2`, observe that
the remainder has degree below `2 * deg Pi` and therefore is divisible by `p`, and push the
quotient of that remainder into `⟨p, Pi⟩`. -/
theorem dvd_exponent_of_minpoly_mem_sq {Pi : ℤ[X]} (hPim : Pi.Monic) (hPid : 0 < Pi.natDegree)
    (hmem : minpoly ℤ θ ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) ^ 2) :
    p ∣ exponent θ := by
  have hfm : (minpoly ℤ θ).Monic := minpoly.monic θ.isIntegral
  have hPi2m : (Pi ^ 2).Monic := hPim.pow 2
  set q := minpoly ℤ θ /ₘ Pi ^ 2 with hqdef
  set r := minpoly ℤ θ %ₘ Pi ^ 2 with hrdef
  have hdiv : r + Pi ^ 2 * q = minpoly ℤ θ := modByMonic_add_div (minpoly ℤ θ) (Pi ^ 2)
  -- The reduction of `Pi ^ 2` divides that of `f`, so `2 * deg Pi ≤ deg f`.
  have hdvdmap : (Pi.map (Int.castRingHom (ZMod p))) ^ 2 ∣
      (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) := by
    obtain ⟨u, v, w, huvw⟩ := Ideal.mem_span_pair_sq_iff.mp hmem
    exact ⟨w.map (Int.castRingHom (ZMod p)), by
      rw [huvw]; simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]⟩
  have hle : 2 * Pi.natDegree ≤ (minpoly ℤ θ).natDegree := by
    have h := Polynomial.natDegree_le_of_dvd hdvdmap (hfm.map _).ne_zero
    rwa [(hPim.map _).natDegree_pow, hPim.natDegree_map, hfm.natDegree_map] at h
  -- The remainder is small, hence divisible by `p`.
  have hrdegPi : r.degree < (Pi ^ 2).degree := degree_modByMonic_lt _ hPi2m
  have hrdegf : r.degree < (minpoly ℤ θ).degree := by
    refine hrdegPi.trans_le ?_
    rw [degree_eq_natDegree hPi2m.ne_zero, degree_eq_natDegree hfm.ne_zero,
      hPim.natDegree_pow]
    exact_mod_cast hle
  have hrmem : r ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) ^ 2 := by
    have hsub : r = minpoly ℤ θ - Pi ^ 2 * q := by linear_combination hdiv
    rw [hsub]
    refine Ideal.sub_mem _ hmem (Ideal.mul_mem_right _ _ ?_)
    rw [sq, sq]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hrsmall : r.natDegree < 2 * Pi.natDegree := by
    have hne1 : Pi ^ 2 ≠ 1 := fun h => by
      have h0 : (Pi ^ 2).natDegree = 0 := by rw [h]; simp
      rw [hPim.natDegree_pow] at h0; omega
    have h := natDegree_modByMonic_lt (minpoly ℤ θ) hPi2m hne1
    rwa [hPim.natDegree_pow] at h
  obtain ⟨s, hs⟩ := C_dvd_of_mem_sq_of_natDegree_lt hPim hrmem hrsmall
  obtain ⟨c, k, hck⟩ := Ideal.mem_span_pair.mp
    (mem_span_pair_of_C_mul_mem_sq (hPim.map _).ne_zero (hs ▸ hrmem))
  -- The quotient is monic, of degree `deg f - 2 * deg Pi`.
  have hPi2q : (Pi ^ 2 * q).Monic := by
    have heq : Pi ^ 2 * q = minpoly ℤ θ - r := by linear_combination hdiv
    rw [heq]; exact hfm.sub_of_left hrdegf
  have hqm : q.Monic := hPi2m.of_mul_monic_left hPi2q
  have hdegeq : (Pi ^ 2 * q).natDegree = (minpoly ℤ θ).natDegree := by
    have heq : Pi ^ 2 * q = minpoly ℤ θ - r := by linear_combination hdiv
    rw [heq]
    exact natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hrdegf)
  refine dvd_exponent_of_sq_factor (h := Pi) (g := q) (k := k) (t := c) (hPim.mul hqm) ?_ ?_
  · rw [hPim.natDegree_mul hqm]
    rw [hPi2m.natDegree_mul hqm, hPim.natDegree_pow] at hdegeq
    omega
  · linear_combination -hdiv + hs - C (p : ℤ) * hck

/-- **Uchida's criterion.**  A rational prime `p` divides the index `[𝓞 K : ℤ[θ]]` if and
only if the minimal polynomial of `θ` lies in the square of a maximal ideal `⟨p, Pi⟩` of
`ℤ[X]`, with `Pi` monic and irreducible mod `p`.

This is the form in which Section 2 of Kaur–Kumar–Remete is stated throughout. -/
theorem dvd_exponent_iff_exists_monic_irreducible_minpoly_mem_sq
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    p ∣ exponent θ ↔ ∃ Pi : ℤ[X], Pi.Monic ∧
      Irreducible (Pi.map (Int.castRingHom (ZMod p))) ∧
      minpoly ℤ θ ∈ (Ideal.span {C (p : ℤ), Pi} : Ideal ℤ[X]) ^ 2 := by
  refine ⟨exists_monic_irreducible_minpoly_mem_sq_of_dvd_exponent hθ, ?_⟩
  rintro ⟨Pi, hPim, hPiirr, hmem⟩
  refine dvd_exponent_of_minpoly_mem_sq hPim ?_ hmem
  -- A monic polynomial of degree `0` is `1`, whose reduction is not irreducible.
  rcases Nat.eq_zero_or_pos Pi.natDegree with h0 | h
  · rw [eq_one_of_monic_natDegree_zero hPim h0] at hPiirr
    simp only [Polynomial.map_one] at hPiirr
    exact absurd hPiirr not_irreducible_one
  · exact h

end RingOfIntegers
